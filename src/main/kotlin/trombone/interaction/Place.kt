package trombone.interaction

import HighwayTools.debugLevel
import HighwayTools.dynamicDelay
import HighwayTools.maxReach
import HighwayTools.placeDelay
import HighwayTools.placeDelayMs
import HighwayTools.raytrace
import HighwayTools.taskTimeout
import com.lambda.client.LambdaMod
import com.lambda.client.event.SafeClientEvent
import com.lambda.client.util.items.blockBlacklist
import com.lambda.client.util.math.CoordinateConverter.asString
import com.lambda.client.util.text.MessageSendHelper
import com.lambda.client.util.threads.defaultScope
import com.lambda.client.util.threads.onMainThreadSafe
import com.lambda.client.util.world.PlaceInfo
import com.lambda.client.util.world.getHitVec
import com.lambda.client.util.world.isReplaceable
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import net.minecraft.network.play.client.CPacketEntityAction
import net.minecraft.network.play.client.CPacketPlayerTryUseItemOnBlock
import net.minecraft.util.EnumFacing
import net.minecraft.util.EnumHand
import net.minecraft.util.math.BlockPos
import net.minecraft.util.math.RayTraceResult
import net.minecraft.util.math.Vec3d
import trombone.IO.DebugLevel
import trombone.Trombone.module
import trombone.handler.Container.containerTask
import trombone.handler.Inventory.lastHitVec
import trombone.handler.Inventory.placeReadyTime
import trombone.handler.Inventory.waitTicks
import trombone.task.BlockTask
import trombone.task.TaskState

object Place {
    var extraPlaceDelay = 0

    /** A block, one of its sides and the exact point on that side the placement is sent against. */
    data class PlaceFace(val pos: BlockPos, val side: EnumFacing, val hitVec: Vec3d)

    fun SafeClientEvent.findPlaceFace(sequence: List<PlaceInfo>, targetPos: BlockPos): PlaceFace? {
        val last = sequence.lastOrNull() ?: return null
        if (!raytrace) return PlaceFace(last.pos, last.side, getHitVec(last.pos, last.side))

        val eyePos = player.getPositionEyes(1f)

        /* The face the sequence wants to use, if the eyes really see it */
        findVisibleHitVec(last.pos, last.side)?.let { return PlaceFace(last.pos, last.side, it) }

        /* Otherwise every solid neighbour of the target is a candidate. This is what lets the wall hang on the ceiling or on its neighbours. */
        return EnumFacing.values().mapNotNull { side ->
            val neighbour = targetPos.offset(side)
            val face = side.opposite

            if (world.getBlockState(neighbour).isReplaceable) return@mapNotNull null

            findVisibleHitVec(neighbour, face)?.let { PlaceFace(neighbour, face, it) }
        }.minByOrNull { eyePos.distanceTo(it.hitVec) }
    }

    /**
     * Strict face check: returns a point on the given face where a ray from the eyes hits exactly this
     * block and this side first (nothing in between), or null if no such point exists.
     * The point is the real ray intersection, so rotation and the sent cursor offset agree with what
     * the server (NCP) will trace itself.
     */
    private fun SafeClientEvent.findVisibleHitVec(pos: BlockPos, side: EnumFacing): Vec3d? {
        val eyePos = player.getPositionEyes(1f)
        val dir = side.directionVec
        val center = Vec3d(pos.x + 0.5 + dir.x * 0.5, pos.y + 0.5 + dir.y * 0.5, pos.z + 0.5 + dir.z * 0.5)

        /* Axes spanning the face */
        val u: Vec3d
        val v: Vec3d
        when (side.axis) {
            EnumFacing.Axis.X -> { u = Vec3d(0.0, 1.0, 0.0); v = Vec3d(0.0, 0.0, 1.0) }
            EnumFacing.Axis.Y -> { u = Vec3d(1.0, 0.0, 0.0); v = Vec3d(0.0, 0.0, 1.0) }
            else -> { u = Vec3d(1.0, 0.0, 0.0); v = Vec3d(0.0, 1.0, 0.0) }
        }

        /* Centre first, then points that stay clear of the face edges (NCP is picky near edges) */
        val steps = doubleArrayOf(0.0, -0.3, 0.3)

        for (a in steps) {
            for (b in steps) {
                val point = center.add(u.scale(a)).add(v.scale(b))
                if (eyePos.distanceTo(point) > maxReach) continue

                /* Trace a bit past the face, a ray ending exactly on the surface can miss the block */
                val end = eyePos.add(point.subtract(eyePos).normalize().scale(eyePos.distanceTo(point) + 1.0))
                val result = world.rayTraceBlocks(eyePos, end, false, false, false) ?: continue

                if (result.typeOfHit != RayTraceResult.Type.BLOCK
                    || result.blockPos != pos
                    || result.sideHit != side
                ) continue

                /* Snap the axis of the side to the exact plane (0.0 or 1.0 offset) */
                val hit = result.hitVec
                return Vec3d(
                    if (dir.x != 0) center.x else hit.x,
                    if (dir.y != 0) center.y else hit.y,
                    if (dir.z != 0) center.z else hit.z
                )
            }
        }

        return null
    }

    fun SafeClientEvent.placeBlock(blockTask: BlockTask) {
        val face = blockTask.placeFace

        if (blockTask.sequence.isEmpty() || face == null) {
            if (debugLevel == DebugLevel.VERBOSE) {
                LambdaMod.LOG.warn("${module.chatName} No neighbours found for ${blockTask.blockPos.asString()}")
            }
            if (blockTask == containerTask) {
                MessageSendHelper.sendChatMessage("${module.chatName} Can't find neighbour blocks to place down the container.")
            }
            if (blockTask == containerTask) {
                blockTask.onStuck(21)
                blockTask.updateState(TaskState.DONE)
            } else {
                /* Can't be placed from here. Not DONE: the task is re-checked every tick and comes back once a face is visible. */
                blockTask.updateState(TaskState.IMPOSSIBLE_PLACE)
            }
            return
        }

        val hitVec = blockTask.placeHitVec ?: getHitVec(face.first, face.second)
        lastHitVec = hitVec

        placeBlockNormal(blockTask, face.first, face.second, hitVec)
    }

    private fun SafeClientEvent.placeBlockNormal(blockTask: BlockTask, placePos: BlockPos, side: EnumFacing, hitVec: Vec3d) {
        /* Cursor offset inside the block, matching the point we rotate to */
        val hitVecOffset = Vec3d(
            (hitVec.x - placePos.x).coerceIn(0.0, 1.0),
            (hitVec.y - placePos.y).coerceIn(0.0, 1.0),
            (hitVec.z - placePos.z).coerceIn(0.0, 1.0)
        )
        val currentBlock = world.getBlockState(placePos).block

        waitTicks = if (dynamicDelay) {
            placeDelay + extraPlaceDelay
        } else {
            placeDelay
        }
        placeReadyTime = System.currentTimeMillis() + placeDelayMs
        blockTask.updateState(TaskState.PENDING_PLACE)

        if (currentBlock in blockBlacklist) {
            connection.sendPacket(CPacketEntityAction(player, CPacketEntityAction.Action.START_SNEAKING))
        }

        defaultScope.launch {
            delay(20L) // ToDo: Check if necessary
            onMainThreadSafe {
                val placePacket = CPacketPlayerTryUseItemOnBlock(placePos, side, EnumHand.MAIN_HAND, hitVecOffset.x.toFloat(), hitVecOffset.y.toFloat(), hitVecOffset.z.toFloat())
                connection.sendPacket(placePacket)
                player.swingArm(EnumHand.MAIN_HAND)
            }

            if (currentBlock in blockBlacklist) {
                delay(20L)
                onMainThreadSafe {
                    connection.sendPacket(CPacketEntityAction(player, CPacketEntityAction.Action.STOP_SNEAKING))
                }
            }

            delay(50L * taskTimeout)
            if (blockTask.taskState == TaskState.PENDING_PLACE) {
                blockTask.updateState(TaskState.PLACE)
                if (dynamicDelay && extraPlaceDelay < 10) extraPlaceDelay += 1
            }
        }
    }
}