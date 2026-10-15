package trombone

import HighwayTools.baritonePath
import HighwayTools.ceiling
import HighwayTools.material
import HighwayTools.maxReach
import HighwayTools.mode
import HighwayTools.moveSpeed
import HighwayTools.refreshTimeout
import HighwayTools.scaffold
import HighwayTools.wallOff
import HighwayTools.width
import com.lambda.client.event.SafeClientEvent
import com.lambda.client.util.BaritoneUtils
import com.lambda.client.util.EntityUtils.flooredPosition
import com.lambda.client.util.TickTimer
import com.lambda.client.util.TimeUnit
import com.lambda.client.util.math.Direction
import com.lambda.client.util.math.VectorUtils.distanceTo
import com.lambda.client.util.math.VectorUtils.multiply
import com.lambda.client.util.math.VectorUtils.toVec3dCenter
import com.lambda.client.util.world.isReplaceable
import net.minecraft.block.BlockLiquid
import net.minecraft.init.Blocks
import net.minecraft.util.EnumFacing
import net.minecraft.util.math.BlockPos
import net.minecraft.util.math.Vec3d
import com.lambda.client.util.text.MessageSendHelper
import trombone.IO.disableError
import trombone.Statistics.simpleMovingAverageDistance
import trombone.Trombone.Structure
import trombone.Trombone.active
import trombone.Trombone.module
import trombone.blueprint.BlueprintGenerator.blueprint
import trombone.handler.Container.containerTask
import trombone.handler.Container.getCollectingPosition
import trombone.handler.Container.grindCycles
import trombone.handler.Inventory.lastHitVec
import trombone.task.TaskManager.isBaseDone
import trombone.task.TaskManager.isBehindPos
import trombone.task.TaskManager.populateTasks
import trombone.task.TaskManager.sortedTasks
import trombone.task.TaskManager.tasks
import trombone.task.BlockTask
import trombone.task.TaskState
import kotlin.math.abs
import kotlin.math.hypot

object Pathfinder {
    var goal: BlockPos? = null
    var moveState = MovementState.RUNNING

    val rubberbandTimer = TickTimer(TimeUnit.TICKS)

    var startingDirection = Direction.NORTH
    var currentBlockPos = BlockPos(0, -1, 0)
    var startingBlockPos = BlockPos(0, -1, 0)
    private var targetBlockPos = BlockPos(0, -1, 0)
    var distancePending = 0

    /* How many ticks the bot already tried to reach a ceiling block, to not get stuck on unreachable ones */
    private val ceilingAttempts = HashMap<BlockPos, Int>()
    private const val CEILING_MAX_ATTEMPTS = 100
    private var ceilingTarget: BlockPos? = null
    private var ceilingStandPos: BlockPos? = null

    /* Ticks spent standing on the stand position while the target is still not placeable */
    private var ceilingArrivedTicks = 0

    /* Stall watchdog: if nothing gets placed, broken or passed for a while, refresh and recover */
    private var lastProgress = -1L
    private var lastProgressPos = BlockPos(0, -1, 0)
    private var lastPlayerPos = Vec3d.ZERO
    private var stallTicks = 0
    private var stallStage = 0

    /* Ticks without progress before the watchdog acts, set by the "Refresh Timeout" setting (seconds) */
    private fun stallTicksLimit() = refreshTimeout * 20

    /*
     * Set by the stall watchdog: the zigzag is paused and the bot stands in the middle of the road until
     * something gets placed or broken again (or the bot moves on to the next row).
     */
    private var forceMiddle = false

    /*
     * Set when ceiling / wall blocks couldn't be placed while zigzagging: from then on the bot stays in the
     * middle of the road and walks to a stand position for the ceiling instead (until the module is re-enabled).
     */
    private var zigzagFallback = false

    /* Ceiling / wall blocks given up on after a stall. They are not retried. */
    val skipped: MutableSet<BlockPos> = java.util.concurrent.ConcurrentHashMap.newKeySet()
    private const val CEILING_MAX_ARRIVED_TICKS = 20

    /*
     * Ceiling / wall blocks that can't be reached from the middle of the road are collected and then built
     * in one trip to the side: the trip starts once the oldest of them is this many rows behind the bot
     * (and would drop out of range if the bot went on). This keeps the bot from zigzagging on every row.
     */
    private const val EDGE_LAG = 2

    enum class MovementState {
        RUNNING, PICKUP, BRIDGE, RESTOCK
    }

    fun SafeClientEvent.setupPathing() {
        moveState = MovementState.RUNNING
        startingBlockPos = player.flooredPosition
        currentBlockPos = startingBlockPos
        startingDirection = Direction.fromEntity(player)
        resetCeiling()
        skipped.clear()
        lastProgress = -1L
        lastProgressPos = currentBlockPos
        lastPlayerPos = player.positionVector
        stallTicks = 0
        stallStage = 0
        forceMiddle = false
        zigzagFallback = false
    }

    private fun resetCeiling() {
        ceilingAttempts.clear()
        ceilingTarget = null
        ceilingStandPos = null
        ceilingArrivedTicks = 0
    }

    /**
     * Called every tick. When the bot made no progress for a while (nothing placed, nothing broken, not a
     * single step forward), the bot goes to the middle of the road and the tasks are thrown away and rebuilt
     * from there, so reach is evaluated fresh. From the middle it crouch-bridges when there is nothing
     * solid to place against (see updatePathing). If that doesn't help it steps one row forward onto solid
     * floor. Ceiling / wall blocks are never skipped. As a last resort the module disables itself and says
     * what blocks it.
     *
     * It never fires while blocks are being mined: a failing break is not a placement stall and a refresh
     * would only throw away the break tasks.
     */
    fun SafeClientEvent.checkStall() {
        val progress = (Statistics.totalBlocksPlaced + Statistics.totalBlocksBroken).toLong()
        val walked = player.positionVector.distanceTo(lastPlayerPos) > 0.5
        val advanced = progress != lastProgress || currentBlockPos != lastProgressPos

        /* While forced to the middle, walking there must not count as progress, or the watchdog never escalates */
        val moved = advanced || (walked && !forceMiddle)

        /* Something is being mined (or a mining attempt is pending / failing): not a stall */
        val mining = tasks.values.any {
            it.taskState == TaskState.BREAK
                    || it.taskState == TaskState.BREAKING
                    || it.taskState == TaskState.PENDING_BREAK
        }

        if (advanced) forceMiddle = false
        if (moved || mining) stallStage = 0

        if (moved || mining || moveState != MovementState.RUNNING || containerTask.taskState != TaskState.DONE) {
            lastProgress = progress
            lastProgressPos = currentBlockPos
            lastPlayerPos = player.positionVector
            stallTicks = 0
            return
        }

        if (++stallTicks < stallTicksLimit()) return
        stallTicks = 0
        stallStage++

        val blockers = tasks.values.filter { it.taskState != TaskState.DONE }
        val description = blockers.take(3).joinToString("\n") { it.prettyPrint() }
            .ifEmpty { "    (no open tasks, waiting to move on)" }

        when (stallStage) {
            1 -> {
                MessageSendHelper.sendWarningMessage("${module.chatName} No progress for ${refreshTimeout}s, moving to the middle and refreshing tasks.\n$description")

                /* Ceiling / wall can't be placed from the zigzag sides: build them from the middle instead */
                if (zigzagEnabled() && blockers.any {
                        (blueprint[it.blockPos]?.isCeiling == true || blueprint[it.blockPos]?.isWall == true)
                                && isUnplaceable(it)
                    }
                ) {
                    zigzagFallback = true
                    MessageSendHelper.sendWarningMessage("${module.chatName} Ceiling can't be placed while zigzagging, building it from the middle of the road instead.")
                }

                forceMiddle = true
                resetState()
            }
            2 -> {
                forceMiddle = true

                /* Walk forward when there is solid floor ahead, the next row may be placeable from there */
                if (canStepForward()) {
                    MessageSendHelper.sendWarningMessage("${module.chatName} Still stuck, stepping one row forward.\n$description")
                    currentBlockPos = currentBlockPos.add(startingDirection.directionVec)
                    lastHitVec = Vec3d.ZERO
                } else {
                    MessageSendHelper.sendWarningMessage("${module.chatName} Still stuck, refreshing tasks again.\n$description")
                }
                resetState()
            }
            else -> {
                disableError("Stuck and unable to recover. Open tasks:\n$description")
            }
        }
    }

    /* Solid floor and free space on the next row, so the bot can simply walk on */
    private fun SafeClientEvent.canStepForward(): Boolean {
        val next = currentBlockPos.add(startingDirection.directionVec)
        return world.isAirBlock(next)
                && world.isAirBlock(next.up())
                && !world.getBlockState(next.down()).isReplaceable
    }

    private fun SafeClientEvent.resetState() {
        tasks.clear()
        sortedTasks.clear()
        resetCeiling()
        moveState = MovementState.RUNNING
        populateTasks()
    }

    /** How far from the middle of the road the bot may stand: never on or next to the outermost column */
    private fun maxLateral() = ((width - 1) / 2 - 1).coerceAtLeast(0)

    /**
     * Wall Off: the bot zigzags. Every row it stands on the other side of the road (left, right, left, ...),
     * so the ceiling edge and the wall hanging from it are within reach on both sides without any
     * stops in the middle. Each edge is reachable from the side it belongs to, either in its own row or
     * the row after, and the bot doesn't move on before that is built.
     */
    private fun zigzagEnabled() = ceiling
            && wallOff
            && mode == Structure.HIGHWAY
            && !startingDirection.isDiagonal
            && maxLateral() > 0
            && !zigzagFallback

    private fun rowIndex(): Int {
        val moved = currentBlockPos.subtract(startingBlockPos)
        val dir = startingDirection.directionVec
        return abs(moved.x * dir.x + moved.z * dir.z)
    }

    /* The spot the bot should stand on for the current row */
    private fun SafeClientEvent.zigzagGoal(): BlockPos {
        if (!zigzagEnabled()) return currentBlockPos

        /* Restocking (placing / opening / grinding a container): stand in the middle, not on the side */
        if (isRestocking()) return currentBlockPos

        /* Stall watchdog asked for the middle */
        if (forceMiddle) return currentBlockPos

        /* The wall / ceiling of this row is built: back to the middle to mine what is left */
        if (!wallWorkPending()) return currentBlockPos

        val side = if (rowIndex() % 2 == 0) 1 else -1
        val lateral = startingDirection.clockwise(2).directionVec

        for (offset in maxLateral() downTo 1) {
            val pos = currentBlockPos.add(lateral.multiply(offset * side))
            if (isInteriorSpot(pos)) return pos
        }

        /* Floor on that side isn't there yet: stay in the middle until it is */
        return currentBlockPos
    }

    /*
     * Ceiling / wall blocks of this row (and the rows behind it) that are not built yet. Only these are the
     * reason to stand on a side of the road.
     */
    private fun wallWorkPending(): Boolean {
        val next = currentBlockPos.add(startingDirection.directionVec).up()
        return tasks.values.any {
            val planned = blueprint[it.blockPos]
            (planned?.isCeiling == true || planned?.isWall == true)
                    && it.taskState != TaskState.DONE
                    && isBehindPos(next, it.blockPos)
        }
    }

    /* A restock is running, waiting for the bot to get back to the middle, or obsidian is being ground */
    private fun isRestocking() = containerTask.taskState != TaskState.DONE
            || grindCycles > 0
            || System.currentTimeMillis() < restockMiddleUntil

    private var restockMiddleUntil = 0L
    private var restockWait = 0

    /**
     * Called before a restock is started. With the zigzag the bot usually stands on a side of the road,
     * where the container can't be placed / reached well, so it first walks back to the middle. Returns
     * true once it is there (or after a few seconds, so a restock can never be blocked forever).
     */
    fun SafeClientEvent.canRestockHere(): Boolean {
        if (!baritonePath || !zigzagEnabled()) {
            restockWait = 0
            return true
        }

        val center = currentBlockPos.toVec3dCenter()
        if (hypot(center.x - player.posX, center.z - player.posZ) < 0.9) {
            restockWait = 0
            return true
        }

        restockMiddleUntil = System.currentTimeMillis() + 250L
        if (++restockWait > 100) {
            restockWait = 0
            return true
        }
        return false
    }

    /* The block that is currently being mined (queued, in progress or pending), the closest one */
    private fun miningTask(): BlockTask? = tasks.values
        .filter {
            it.taskState == TaskState.BREAK
                    || it.taskState == TaskState.BREAKING
                    || it.taskState == TaskState.PENDING_BREAK
        }
        .minByOrNull { it.eyeDistance }

    /**
     * While mining the bot stands still. Only when the block is almost out of reach it takes a step
     * towards it; null means stay where you are.
     */
    private fun SafeClientEvent.approachPos(task: BlockTask): BlockPos? {
        if (task.eyeDistance <= maxReach - 0.5) return null

        val target = task.blockPos.toVec3dCenter()
        val ddx = target.x - player.posX
        val ddz = target.z - player.posZ
        val sx = if (abs(ddx) > 0.75) (if (ddx > 0) 1 else -1) else 0
        val sz = if (abs(ddz) > 0.75) (if (ddz > 0) 1 else -1) else 0

        val feet = player.flooredPosition
        return listOf(feet.add(sx, 0, sz), feet.add(sx, 0, 0), feet.add(0, 0, sz)).firstOrNull {
            it != feet
                    && world.isAirBlock(it)
                    && world.isAirBlock(it.up())
                    && !world.getBlockState(it.down()).isReplaceable
                    && (blueprint[it]?.targetBlock ?: Blocks.AIR) == Blocks.AIR
        }
    }

    /* Close enough to the current row to move on. With the zigzag only the distance along the road counts. */
    private fun SafeClientEvent.closeToRow(): Boolean {
        val center = currentBlockPos.toVec3dCenter()
        if (!zigzagEnabled()) return player.positionVector.distanceTo(center) < 2

        val dir = startingDirection.directionVec
        val along = abs((player.posX - center.x) * dir.x + (player.posZ - center.z) * dir.z)
        return along < 2
    }

    /* The block is not needed when the two wall blocks below it are already there */
    private fun SafeClientEvent.isCeilingSkippable(pos: BlockPos) =
        world.getBlockState(pos.down()).block == material
                && world.getBlockState(pos.down(2)).block == material

    /**
     * Once the highway is built, finds a ceiling block that is missing and can't be worked on from the
     * current position (out of reach) and returns a spot on the road to stand on to reach it.
     *
     * The bot stays on that spot until every ceiling task is done and only then walks on, so it
     * doesn't run back and forth between the centre of the road and the edges.
     */
    private fun SafeClientEvent.getCeilingStandPos(): BlockPos? {
        if (!ceiling || mode != Structure.HIGHWAY || zigzagEnabled() || !isBaseDone()) {
            ceilingTarget = null
            ceilingStandPos = null
            ceilingArrivedTicks = 0
            return null
        }

        /* Stick to the current target until it is built (or given up on) */
        ceilingTarget?.let { target ->
            val attempts = (ceilingAttempts[target] ?: 0) + 1
            ceilingAttempts[target] = attempts

            /*
             * Standing right on the spot and the block still can't be placed (no visible face from
             * here with Raytrace): give up on it instead of waiting there, so the bot keeps going.
             */
            val standPos = ceilingStandPos
            if (standPos != null && player.positionVector.distanceTo(standPos.toVec3dCenter()) < 1.5) {
                ceilingArrivedTicks++
                if (ceilingArrivedTicks > CEILING_MAX_ARRIVED_TICKS && isUnplaceable(tasks[target])) {
                    ceilingAttempts[target] = CEILING_MAX_ATTEMPTS
                }
            }

            if (isCeilingMissing(target)
                && (ceilingAttempts[target] ?: 0) < CEILING_MAX_ATTEMPTS
                && attempts < CEILING_MAX_ATTEMPTS
            ) return ceilingStandPos

            ceilingTarget = null
            ceilingArrivedTicks = 0
        }

        val eyePos = player.getPositionEyes(1f)
        val nextPos = currentBlockPos.add(startingDirection.directionVec).up()
        val startPad = startingBlockPos.add(startingDirection.directionVec)
        val dirVec = startingDirection.directionVec

        /* Blocks further back than this are out of range for good, blocks at least this far back are due */
        val tooFarBack = currentBlockPos.subtract(dirVec.multiply(EDGE_LAG))
        val dueOrigin = currentBlockPos.subtract(dirVec.multiply(EDGE_LAG - 1))

        val candidates = blueprint.entries.asSequence()
            .filter { (pos, blueprintTask) ->
                (blueprintTask.isCeiling || blueprintTask.isWall)
                        && pos !in skipped
                        && !(blueprintTask.isCeiling && isCeilingSkippable(pos))
                        && (ceilingAttempts[pos] ?: 0) < CEILING_MAX_ATTEMPTS
                        && isBehindPos(nextPos, pos)
                        && !isBehindPos(tooFarBack, pos)
                        && !isBehindPos(startPad, pos)
                        && currentBlockPos.distanceTo(pos) <= width + 3
                        && isCeilingMissing(pos)
                        && tasks[pos].let { task ->
                    task == null
                            || isUnplaceable(task)
                }
            }
            .map { it.key }
            .toList()

        /* Not worth a trip yet: wait until the oldest missing block is about to drop out of range */
        val due = candidates.any { isBehindPos(dueOrigin, it) }

        for (target in (if (due) candidates.sortedBy { eyePos.distanceTo(it.toVec3dCenter()) } else emptyList())) {
            val standPos = findStandPos(target)

            if (standPos == null) {
                ceilingAttempts[target] = CEILING_MAX_ATTEMPTS
                continue
            }

            /* Walking there only makes sense when the block is actually in reach from that spot */
            val standEyes = Vec3d(standPos.x + 0.5, standPos.y + 1.62, standPos.z + 0.5)
            if (standEyes.distanceTo(target.toVec3dCenter()) > maxReach) {
                ceilingAttempts[target] = CEILING_MAX_ATTEMPTS
                continue
            }

            ceilingTarget = target
            ceilingStandPos = standPos
            ceilingArrivedTicks = 0
            ceilingAttempts[target] = 1
            return standPos
        }

        /* Nothing left that is out of reach: stay put until the remaining tasks are finished */
        if (!isIdle()) return ceilingStandPos

        ceilingStandPos = null
        return null
    }

    private fun SafeClientEvent.isCeilingMissing(pos: BlockPos) =
        world.getBlockState(pos).let {
            it.block != material && it.getBlockHardness(world, pos) >= 0
        }

    /* No task is waiting for or doing something right now */
    private fun isIdle() = tasks.values.none {
        it.taskState != TaskState.DONE && !isUnplaceable(it)
    }

    /* A block that can't be placed from here (no neighbour, or no face visible from the eyes) */
    private fun isUnplaceable(task: BlockTask?) = task != null
            && (task.taskState == TaskState.IMPOSSIBLE_PLACE
            || (task.taskState == TaskState.PLACE && task.sequence.isEmpty()))

    /*
     * A spot to stand on to reach the target. It
     *  - stays on the current row on straight highways (only steps sideways, never forwards/backwards),
     *  - stays close to the middle of the road (never on or next to the edge / railing),
     *  - is a free spot whose floor and the floor around it is solid, so it can't be the railing or the edge.
     */
    private fun SafeClientEvent.findStandPos(target: BlockPos): BlockPos? {
        val dir = startingDirection.directionVec
        val cardinal = dir.x == 0 || dir.z == 0

        /* How far from the middle the bot may go: stay at least two columns away from the edge */
        val maxLateral = maxLateral()
        val cx = currentBlockPos.x
        val cz = currentBlockPos.z

        val bx = if (cardinal && dir.x != 0) cx else cx + (target.x - cx).coerceIn(-maxLateral, maxLateral)
        val bz = if (cardinal && dir.z != 0) cz else cz + (target.z - cz).coerceIn(-maxLateral, maxLateral)
        val base = BlockPos(bx, currentBlockPos.y, bz)

        val sx = if (cardinal && dir.x != 0) 0 else Integer.signum(cx - bx)
        val sz = if (cardinal && dir.z != 0) 0 else Integer.signum(cz - bz)

        return listOf(
            base,
            base.add(sx, 0, 0),
            base.add(0, 0, sz),
            base.add(sx, 0, sz),
            base.add(sx * 2, 0, 0),
            base.add(0, 0, sz * 2),
            base.add(sx * 2, 0, sz * 2)
        ).firstOrNull {
            abs(it.x - cx) <= maxLateral && abs(it.z - cz) <= maxLateral && isInteriorSpot(it)
        }
    }

    /*
     * Free to stand in, not a railing position, with floor below, and no way to step off sideways: each
     * side is either floor or something solid at feet level (the railing). Only the sides across the road
     * count, the floor ahead may not be placed yet.
     */
    private fun SafeClientEvent.isInteriorSpot(pos: BlockPos): Boolean {
        if (!world.isAirBlock(pos) || !world.isAirBlock(pos.up())) return false

        val planned = blueprint[pos]?.targetBlock
        if (planned != null && planned != Blocks.AIR) return false

        if (world.getBlockState(pos.down()).isReplaceable) return false

        val dir = startingDirection.directionVec
        val sides = when {
            startingDirection.isDiagonal -> listOf(EnumFacing.NORTH, EnumFacing.EAST, EnumFacing.SOUTH, EnumFacing.WEST)
            dir.x != 0 -> listOf(EnumFacing.NORTH, EnumFacing.SOUTH)
            else -> listOf(EnumFacing.EAST, EnumFacing.WEST)
        }

        return sides.all {
            val next = pos.offset(it)
            !world.getBlockState(next.down()).isReplaceable || !world.isAirBlock(next)
        }
    }

    /**
     * Sends Baritone to [pos]. Only when the bot ended up on top of the railing it is pushed back into the
     * road directly, so it doesn't walk along the rail or fall off the outside.
     */
    private fun SafeClientEvent.steerTo(pos: BlockPos) {
        val center = pos.toVec3dCenter()
        val dist = hypot(center.x - player.posX, center.z - player.posZ)
        val heightAbove = player.posY - pos.y
        val onRailing = mode == Structure.HIGHWAY && player.onGround && heightAbove > 0.5 && heightAbove < 1.6

        if (onRailing && dist < 4.0) {
            goal = null
            moveTo(center)
        } else {
            goal = pos
        }
    }

    fun SafeClientEvent.updatePathing() {
        runPathing()

        /* Toggle Baritone Path off: never steer the player, the user walks */
        if (!baritonePath) goal = null
    }

    private fun SafeClientEvent.runPathing() {
        when (moveState) {
            MovementState.RUNNING -> {
                /*
                 * Mining: stand still, only step closer when the block is almost out of reach. Once the
                 * block is gone the normal goal below brings the bot back to where it belongs.
                 */
                val mining = if (isRestocking()) null else miningTask()

                if (mining != null) {
                    val closer = approachPos(mining)
                    if (closer != null) steerTo(closer) else goal = null
                } else {
                    /* Head for the middle of the road, or for this row's side when zigzagging */
                    steerTo(zigzagGoal())
                }

                /*
                 * After a stall, once standing in the middle: when there is nothing solid left to place
                 * against, crouch and bridge forward (the placement rotates to the face it needs).
                 */
                if (mining == null
                    && forceMiddle
                    && player.positionVector.distanceTo(currentBlockPos.toVec3dCenter()) < 1
                    && shouldBridge()
                ) {
                    moveState = MovementState.BRIDGE
                    return
                }

                // ToDo: Rewrite
                if (currentBlockPos.distanceTo(targetBlockPos) < 2 ||
                    (distancePending > 0 &&
                            startingBlockPos.add(
                                startingDirection.directionVec.multiply(distancePending)
                            ).distanceTo(currentBlockPos) == 0.0)) {
                    disableError("Reached target destination")
                    return
                }

                /* Walk to the part of the road needed to reach the ceiling */
                if (mining == null) {
                    getCeilingStandPos()?.let {
                        steerTo(it)
                        return
                    }
                }

                val possiblePos = currentBlockPos.add(startingDirection.directionVec)

                if (!isTaskDone(possiblePos.up())
                    || !isTaskDone(possiblePos)
                    || !isTaskDone(possiblePos.down())
                ) return

                if (!checkForResidue(possiblePos.up())) return

                if (world.getBlockState(possiblePos.down()).isReplaceable) return

                if (currentBlockPos != possiblePos && closeToRow()) {
                    simpleMovingAverageDistance.add(System.currentTimeMillis())
                    lastHitVec = Vec3d.ZERO
                    currentBlockPos = possiblePos
                    populateTasks()
                }
            }
            MovementState.BRIDGE -> {
                goal = null
                val isAboveAir = world.getBlockState(player.flooredPosition.down()).isReplaceable
                if (isAboveAir && baritonePath) player.movementInput?.sneak = true
                if (shouldBridge()) {
                    val target = currentBlockPos.toVec3dCenter().add(Vec3d(startingDirection.directionVec))
                    moveTo(target)
                } else {
                    if (!isAboveAir) {
                        moveState = MovementState.RUNNING
                    }
                }
            }
            MovementState.PICKUP -> {
                goal = getCollectingPosition()
            }
            MovementState.RESTOCK -> {
                val target = currentBlockPos.toVec3dCenter()
                if (player.positionVector.distanceTo(target) < 2) {
                    goal = null
                    moveTo(target)
                } else {
                    goal = currentBlockPos
                }
            }
        }
    }

    private fun checkForResidue(pos: BlockPos) =
        containerTask.taskState == TaskState.DONE
                && tasks.values.all {
            it.taskState == TaskState.DONE
                    || !isBehindPos(pos, it.blockPos)
                    /* a ceiling block that can't be placed must not hold the bot back */
                    || (isUnplaceable(it)
                    && (blueprint[it.blockPos]?.isCeiling == true || blueprint[it.blockPos]?.isWall == true))
        }

    private fun SafeClientEvent.isTaskDone(pos: BlockPos): Boolean {
        val block = world.getBlockState(pos).block
        return tasks[pos]?.let {
            it.taskState == TaskState.DONE
                    && block != Blocks.PORTAL
                    && block != Blocks.END_PORTAL
                    && block !is BlockLiquid
        } ?: false
    }

    fun SafeClientEvent.shouldBridge(): Boolean {
        return scaffold
                && containerTask.taskState == TaskState.DONE
                && world.isAirBlock(currentBlockPos.add(startingDirection.directionVec))
                && world.isAirBlock(currentBlockPos.add(startingDirection.directionVec).up())
                && world.getBlockState(currentBlockPos.add(startingDirection.directionVec).down()).isReplaceable
                && tasks.values.none { it.taskState == TaskState.PENDING_PLACE }
                && tasks.values.filter {
            (it.taskState == TaskState.PLACE
                    || it.taskState == TaskState.LIQUID)
                    /* ceiling tasks wait for the floor, so they must not block bridging */
                    && blueprint[it.blockPos]?.isCeiling != true
                    && blueprint[it.blockPos]?.isWall != true
        }.none { it.sequence.isNotEmpty() }
    }

    private fun SafeClientEvent.moveTo(target: Vec3d) {
        if (!baritonePath) return
        player.motionX = (target.x - player.posX).coerceIn((-moveSpeed).toDouble(), moveSpeed.toDouble())
        player.motionZ = (target.z - player.posZ).coerceIn((-moveSpeed).toDouble(), moveSpeed.toDouble())
    }

    fun updateProcess() {
        if (!active) {
            active = true
            BaritoneUtils.primary?.pathingControlManager?.registerProcess(Process)
        }
    }

    fun clearProcess() {
        active = false
        goal = null
    }
}