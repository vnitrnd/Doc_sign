package com.docsign.app

import android.content.ContentValues
import android.content.Context
import android.content.Intent
import android.graphics.Bitmap
import android.graphics.Canvas as AndroidCanvas
import android.graphics.Color as AndroidColor
import android.graphics.Paint
import android.graphics.pdf.PdfDocument
import android.graphics.pdf.PdfRenderer
import android.graphics.SurfaceTexture
import android.net.ConnectivityManager
import android.net.Network
import android.net.Uri
import android.view.TextureView
import androidx.core.view.WindowCompat
import java.util.concurrent.CountDownLatch
import android.os.Build
import android.os.Bundle
import android.widget.Toast
import android.os.Environment
import android.os.Handler
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.provider.MediaStore
import androidx.activity.ComponentActivity
import androidx.activity.compose.BackHandler
import androidx.activity.compose.setContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.FastOutSlowInEasing
import androidx.compose.animation.core.animate
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.border
import androidx.compose.foundation.clickable
import androidx.compose.foundation.gestures.awaitEachGesture
import androidx.compose.foundation.gestures.awaitFirstDown
import androidx.compose.foundation.gestures.calculateCentroid
import androidx.compose.foundation.gestures.calculatePan
import androidx.compose.foundation.gestures.calculateZoom
import androidx.compose.foundation.gestures.detectDragGestures
import androidx.compose.foundation.gestures.detectTapGestures
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.Redo
import androidx.compose.material.icons.automirrored.filled.Undo
import androidx.compose.material.icons.filled.BookmarkAdd
import androidx.compose.material.icons.filled.Delete
import androidx.compose.material.icons.filled.FolderSpecial
import androidx.compose.material.icons.filled.Home
import androidx.compose.material.icons.filled.PictureAsPdf
import androidx.compose.material.icons.filled.Share
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.draw.shadow
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.graphics.PathEffect
import androidx.compose.ui.graphics.RectangleShape
import androidx.compose.ui.graphics.StrokeCap
import androidx.compose.ui.graphics.StrokeJoin
import androidx.compose.ui.graphics.TransformOrigin
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.graphics.drawscope.Stroke
import androidx.compose.ui.graphics.drawscope.drawIntoCanvas
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.graphics.nativeCanvas
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.input.pointer.util.VelocityTracker
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.layout.onSizeChanged
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.compose.ui.viewinterop.AndroidView
import androidx.compose.ui.window.Dialog
import androidx.compose.ui.window.DialogProperties
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.ui.text.font.FontFamily
import androidx.compose.ui.text.input.KeyboardCapitalization
import androidx.compose.material.icons.filled.Lock
import androidx.compose.ui.ExperimentalComposeUiApi
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Job
import kotlinx.coroutines.launch
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.collectLatest
import okhttp3.MediaType.Companion.toMediaType
import okhttp3.MultipartBody
import okhttp3.OkHttpClient
import okhttp3.Request
import okhttp3.RequestBody.Companion.asRequestBody
import okhttp3.RequestBody.Companion.toRequestBody
import okhttp3.Response
import okhttp3.WebSocket
import okhttp3.WebSocketListener
import org.json.JSONObject
import org.webrtc.*
import java.io.File
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.math.abs
import kotlin.math.exp
import kotlin.math.ln
import kotlin.math.pow
import kotlin.math.roundToInt
import kotlin.math.sqrt

private const val BACKEND_BASE_URL = "https://docsign-backend-c8ka.onrender.com"
private const val BACKEND_WEBSOCKET_URL = "wss://docsign-backend-c8ka.onrender.com"
private const val BACKEND_UPLOAD_URL = "$BACKEND_BASE_URL/api/documents/upload"

// ---- Pairing code: must match the code shown on the host PC. Everything on the server is scoped to it. ----
@Volatile private var lastCaptureDetected = true          // did the host find the page edges in the last capture?
private const val PAIR_CODE_LEN = 8                       // shown on the host as XXXX-XXXX
private var pairCode by mutableStateOf("")
private var pairNotice by mutableStateOf<String?>(null)
private var pairKeyCache: Pair<String, String>? = null

/**
 * The server never sees the typed code. Both sides derive a 64-hex key from it with PBKDF2-HMAC-SHA256
 * (same salt / iterations as the host) and only that key is sent, so a leaked server log reveals nothing usable.
 */
private fun derivePairKey(code: String): String {
    val pw = code.uppercase().filter { it.isLetterOrDigit() }.toByteArray(Charsets.US_ASCII)
    val salt = "docsign-pair-v1".toByteArray(Charsets.US_ASCII)
    val mac = javax.crypto.Mac.getInstance("HmacSHA256")
    mac.init(javax.crypto.spec.SecretKeySpec(pw, "HmacSHA256"))
    var u = mac.doFinal(salt + byteArrayOf(0, 0, 0, 1))
    val t = u.copyOf()
    for (i in 1 until 60000) {
        u = mac.doFinal(u)
        for (k in t.indices) t[k] = (t[k].toInt() xor u[k].toInt()).toByte()
    }
    return t.joinToString("") { "%02x".format(it) }
}

@Synchronized
private fun pairKey(): String {
    val code = pairCode
    if (code.length != PAIR_CODE_LEN) return ""
    pairKeyCache?.let { if (it.first == code) return it.second }
    val key = derivePairKey(code)
    pairKeyCache = code to key
    return key
}

private fun warmPairKey() {
    if (pairCode.length == PAIR_CODE_LEN) Thread { try { pairKey() } catch (e: Exception) {} }.start()
}

/**
 * The pairing code lives in memory ONLY. It is never written to disk, so closing the app (swiping it out of the
 * recent apps list) always means the code must be typed again. Any code saved by an older version is wiped here.
 */
private fun wipeStoredPairCode(context: Context) {
    try { context.getSharedPreferences("docsign", Context.MODE_PRIVATE).edit().remove("pair_code").apply() } catch (e: Exception) {}
}

private fun savePairCode(code: String) {
    pairCode = code
    pairKeyCache = null
    warmPairKey()
}

private const val ASSUMED_PAGE_WIDTH_PTS = 595
private const val ASSUMED_PAGE_HEIGHT_PTS = 842

private enum class Screen { LiveFeed, Crop, Doodle, WatchSigning, PauseConfirm }

@Volatile
private var signalingWebSocket: WebSocket? = null
@Volatile
private var isSignalingConnected: Boolean = false
@Volatile
private var pendingCaptureRequest: Boolean = false

// Reported by the host PC. false = host runs in camera-only mode (live view works, nothing can be drawn).
private var hostMachineConnected by mutableStateOf(true)

/**
 * Builds a one-page PDF: the scanned page as the background image, and the signature/annotation strokes drawn
 * on top as real vector paths (PdfDocument's canvas writes paths as PDF drawing operators, not pixels), so
 * they stay sharp at any zoom. Stroke points are in the same pixel space as [bitmap].
 */
private fun buildPdfDocument(
    bitmap: Bitmap,
    strokes: List<List<Offset>> = emptyList(),
    strokeWidths: List<Float> = emptyList()
): PdfDocument {
    val pdfDocument = PdfDocument()
    val pageInfo = PdfDocument.PageInfo.Builder(bitmap.width, bitmap.height, 1).create()
    val page = pdfDocument.startPage(pageInfo)
    val canvas = page.canvas
    canvas.drawBitmap(bitmap, 0f, 0f, null)
    val paint = Paint().apply {
        color = AndroidColor.rgb(30, 58, 138)
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
        isAntiAlias = true
    }
    strokes.forEachIndexed { i, stroke ->
        if (stroke.isEmpty()) return@forEachIndexed
        paint.strokeWidth = (strokeWidths.getOrElse(i) { 1f }).coerceAtLeast(2.0f)
        if (stroke.size == 1) {
            // a single tap: draw a dot (zero-length lines are dropped by some PDF viewers)
            paint.style = Paint.Style.FILL
            canvas.drawCircle(stroke[0].x, stroke[0].y, paint.strokeWidth / 2f, paint)
            paint.style = Paint.Style.STROKE
        } else {
            val path = android.graphics.Path()
            path.moveTo(stroke[0].x, stroke[0].y)
            for (k in 1 until stroke.size) path.lineTo(stroke[k].x, stroke[k].y)
            canvas.drawPath(path, paint)
        }
    }
    pdfDocument.finishPage(page)
    return pdfDocument
}

private fun saveBitmapAsPdf(
    context: Context,
    bitmap: Bitmap,
    title: String,
    strokes: List<List<Offset>> = emptyList(),
    strokeWidths: List<Float> = emptyList()
): String? {
    return try {
        val pdfDocument = buildPdfDocument(bitmap, strokes, strokeWidths)

        val fileName = "$title.pdf"
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            val contentValues = ContentValues().apply {
                put(MediaStore.MediaColumns.DISPLAY_NAME, fileName)
                put(MediaStore.MediaColumns.MIME_TYPE, "application/pdf")
                put(MediaStore.MediaColumns.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS)
            }
            val uri = context.contentResolver.insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, contentValues)
            if (uri != null) {
                context.contentResolver.openOutputStream(uri)?.use { out ->
                    pdfDocument.writeTo(out)
                }
                pdfDocument.close()
                "Saved to Downloads/$fileName"
            } else null
        } else {
            @Suppress("DEPRECATION")
            val downloadsDir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS)
            var file = File(downloadsDir, fileName)
            var n = 2
            while (file.exists()) { file = File(downloadsDir, "${title}_$n.pdf"); n++ }
            file.outputStream().use { out ->
                pdfDocument.writeTo(out)
            }
            pdfDocument.close()
            "Saved to Downloads/${file.name}"
        }
    } catch (e: Exception) {
        e.printStackTrace()
        null
    }
}

/** Renders the page as a PDF, keeps a copy in Downloads (Android 10+) and opens the system share sheet. */
private fun shareBitmapAsPdf(
    context: Context,
    bitmap: Bitmap,
    title: String,
    strokes: List<List<Offset>> = emptyList(),
    strokeWidths: List<Float> = emptyList()
): String? {
    if (Build.VERSION.SDK_INT < Build.VERSION_CODES.Q) {
        // Old devices: just save it; sharing a raw file path is not allowed there without a FileProvider.
        return saveBitmapAsPdf(context, bitmap, title, strokes, strokeWidths)?.let { "$it - open Files to share it" }
    }
    return try {
        val pdfDocument = buildPdfDocument(bitmap, strokes, strokeWidths)

        val fileName = "$title.pdf"
        val values = ContentValues().apply {
            put(MediaStore.MediaColumns.DISPLAY_NAME, fileName)
            put(MediaStore.MediaColumns.MIME_TYPE, "application/pdf")
            put(MediaStore.MediaColumns.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS)
        }
        val uri = context.contentResolver.insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values)
        if (uri == null) {
            pdfDocument.close()
            null
        } else {
            context.contentResolver.openOutputStream(uri)?.use { out -> pdfDocument.writeTo(out) }
            pdfDocument.close()
            val send = Intent(Intent.ACTION_SEND).apply {
                type = "application/pdf"
                putExtra(Intent.EXTRA_STREAM, uri)
                putExtra(Intent.EXTRA_SUBJECT, "Scanned document")
                addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
            }
            val chooser = Intent.createChooser(send, "Share scanned document").apply {
                addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
                if (context !is android.app.Activity) addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            }
            context.startActivity(chooser)
            "Choose where to share (copy kept in Downloads/$fileName)"
        }
    } catch (e: Exception) {
        e.printStackTrace()
        null
    }
}

@Stable
private class SmoothZoomState(
    private val minScale: Float = 1f,
    private val maxScale: Float = 6f
) {
    var scale by mutableStateOf(1f)
        private set
    var offset by mutableStateOf(Offset.Zero)
        private set
    var viewSize: IntSize = IntSize.Zero
    private var job: Job? = null

    private fun lowBound(size: Float, s: Float) = if (s >= 1f) size * (1f - s) else size * (1f - s) / 2f
    private fun highBound(size: Float, s: Float) = if (s >= 1f) 0f else size * (1f - s) / 2f

    private fun hardClamp(o: Offset, s: Float): Offset {
        val w = viewSize.width.toFloat()
        val h = viewSize.height.toFloat()
        return Offset(
            o.x.coerceIn(minOf(lowBound(w, s), highBound(w, s)), maxOf(lowBound(w, s), highBound(w, s))),
            o.y.coerceIn(minOf(lowBound(h, s), highBound(h, s)), maxOf(lowBound(h, s), highBound(h, s)))
        )
    }

    private fun softAxis(cur: Float, desired: Float, lo: Float, hi: Float, limit: Float): Float {
        if (desired in lo..hi) return desired
        val bound = if (desired > hi) hi else lo
        val curOver = when {
            cur > hi -> cur - hi
            cur < lo -> lo - cur
            else -> 0f
        }
        val desiredOver = abs(desired - bound)
        val over = if (desiredOver <= curOver) {
            desiredOver
        } else {
            val room = (1f - (curOver / limit).coerceIn(0f, 1f))
            curOver + (desiredOver - curOver) * 0.55f * room * sqrt(room)
        }
        return if (desired > hi) hi + over else lo - over
    }

    fun cancelAnimation() {
        job?.cancel()
        job = null
    }

    fun transformBy(centroid: Offset, pan: Offset, zoomChange: Float) {
        if (viewSize == IntSize.Zero || zoomChange <= 0f || zoomChange.isNaN()) return
        val s0 = scale
        val s1 = exp(softAxis(ln(s0), ln(s0 * zoomChange), ln(minScale), ln(maxScale), 0.30f))
        val eff = s1 / s0
        val w = viewSize.width.toFloat()
        val h = viewSize.height.toFloat()
        val raw = centroid + pan - (centroid - offset) * eff
        scale = s1
        offset = Offset(
            softAxis(offset.x, raw.x, minOf(lowBound(w, s1), highBound(w, s1)), maxOf(lowBound(w, s1), highBound(w, s1)), w * 0.15f),
            softAxis(offset.y, raw.y, minOf(lowBound(h, s1), highBound(h, s1)), maxOf(lowBound(h, s1), highBound(h, s1)), h * 0.15f)
        )
    }

    private fun animateTo(scope: CoroutineScope, s1: Float, o1: Offset, anchor: Offset, spec: AnimationSpec<Float>) {
        job?.cancel()
        val s0 = scale
        val o0 = offset
        val anchoredEnd = anchor - (anchor - o0) * (s1 / s0)
        val correction = o1 - anchoredEnd
        job = scope.launch {
            animate(0f, 1f, animationSpec = spec) { p, _ ->
                val s = s0 * (s1 / s0).pow(p)
                scale = s
                offset = anchor - (anchor - o0) * (s / s0) + correction * p
            }
            scale = s1
            offset = o1
        }
    }

    fun animateReset(scope: CoroutineScope) {
        val centre = Offset(viewSize.width / 2f, viewSize.height / 2f)
        animateTo(scope, 1f, Offset.Zero, centre, tween(280, easing = FastOutSlowInEasing))
    }

    fun doubleTap(scope: CoroutineScope, pos: Offset) {
        if (viewSize == IntSize.Zero) return
        if (scale > 1.05f) {
            animateReset(scope)
        } else {
            val s1 = 2.5f
            val o1 = hardClamp(pos - (pos - offset) * (s1 / scale), s1)
            animateTo(scope, s1, o1, pos, tween(300, easing = FastOutSlowInEasing))
        }
    }

    private fun settle(scope: CoroutineScope, anchor: Offset) {
        val s0 = scale
        val s1 = s0.coerceIn(minScale, maxScale)
        val o1 = hardClamp(anchor - (anchor - offset) * (s1 / s0), s1)
        if (abs(s1 - s0) < 0.0005f && (o1 - offset).getDistance() < 0.5f) return
        animateTo(scope, s1, o1, anchor, spring(dampingRatio = 1f, stiffness = 380f))
    }

    private fun fling(scope: CoroutineScope, velocity: Offset) {
        job?.cancel()
        job = scope.launch {
            var v = velocity
            var last = withFrameNanos { it }
            while (v.getDistance() > 30f) {
                val now = withFrameNanos { it }
                val dt = ((now - last) / 1_000_000_000f).coerceIn(0f, 0.05f)
                last = now
                v *= exp(-3.6f * dt)
                val s = scale
                val w = viewSize.width.toFloat()
                val h = viewSize.height.toFloat()
                val loX = minOf(lowBound(w, s), highBound(w, s)); val hiX = maxOf(lowBound(w, s), highBound(w, s))
                val loY = minOf(lowBound(h, s), highBound(h, s)); val hiY = maxOf(lowBound(h, s), highBound(h, s))
                var nx = offset.x + v.x * dt
                var ny = offset.y + v.y * dt
                if (nx < loX) { nx = loX; v = Offset(0f, v.y) } else if (nx > hiX) { nx = hiX; v = Offset(0f, v.y) }
                if (ny < loY) { ny = loY; v = Offset(v.x, 0f) } else if (ny > hiY) { ny = hiY; v = Offset(v.x, 0f) }
                offset = Offset(nx, ny)
            }
        }
    }

    fun onGestureEnd(scope: CoroutineScope, velocity: Offset, anchor: Offset) {
        val w = viewSize.width.toFloat()
        val h = viewSize.height.toFloat()
        val s = scale
        val inside = s >= minScale - 0.001f && s <= maxScale + 0.001f &&
                offset.x >= minOf(lowBound(w, s), highBound(w, s)) - 0.5f && offset.x <= maxOf(lowBound(w, s), highBound(w, s)) + 0.5f &&
                offset.y >= minOf(lowBound(h, s), highBound(h, s)) - 0.5f && offset.y <= maxOf(lowBound(h, s), highBound(h, s)) + 0.5f
        if (!inside) {
            settle(scope, anchor)
        } else if (s > 1.02f) {
            val speed = velocity.getDistance()
            if (speed > 200f) fling(scope, if (speed > 7000f) velocity * (7000f / speed) else velocity)
        }
    }
}

private fun Modifier.smoothZoomGestures(
    state: SmoothZoomState,
    scope: CoroutineScope,
    enabled: () -> Boolean = { true }
): Modifier = this
    .pointerInput(state) {
        detectTapGestures(onDoubleTap = { pos -> if (enabled()) state.doubleTap(scope, pos) })
    }
    .pointerInput(state) {
        awaitEachGesture {
            val first = awaitFirstDown(requireUnconsumed = false)
            state.cancelAnimation()
            var tracker = VelocityTracker()
            tracker.addPosition(first.uptimeMillis, first.position)
            var pastSlop = false
            var interacted = false
            var lastPressed = 1
            var lastCentroid = first.position
            var accumulated = Offset.Zero
            val slop = viewConfiguration.touchSlop
            do {
                val event = awaitPointerEvent()
                if (event.changes.any { it.isConsumed } || !enabled()) break
                val pressedNow = event.changes.count { it.pressed }
                if (pressedNow > 0) {
                    if (pressedNow != lastPressed) {
                        tracker = VelocityTracker()
                        lastPressed = pressedNow
                    }
                    val prevC = event.calculateCentroid(useCurrent = false)
                    val curC = event.calculateCentroid(useCurrent = true)
                    val zoom = event.calculateZoom()
                    val pan = event.calculatePan()
                    val valid = !(prevC.x.isNaN() || prevC.y.isNaN() || curC.x.isNaN() || curC.y.isNaN())
                    if (valid) {
                        if (!pastSlop) {
                            if (pressedNow >= 2) {
                                pastSlop = true
                            } else {
                                accumulated += pan
                                if (accumulated.getDistance() > slop) pastSlop = true
                            }
                        }
                        if (pastSlop) {
                            if (zoom != 1f || pan != Offset.Zero) {
                                state.transformBy(prevC, pan, zoom)
                                interacted = true
                            }
                            event.changes.forEach { if (it.position != it.previousPosition) it.consume() }
                        }
                        lastCentroid = curC
                        tracker.addPosition(event.changes[0].uptimeMillis, curC)
                    }
                }
            } while (event.changes.any { it.pressed })
            if (interacted) {
                val v = tracker.calculateVelocity()
                state.onGestureEnd(scope, Offset(v.x, v.y), lastCentroid)
            }
        }
    }

class MainActivity : ComponentActivity() {

    private var pdfPageBitmap by mutableStateOf<Bitmap?>(null)
    private var signedPreviewBitmap by mutableStateOf<Bitmap?>(null)
    private var documentId by mutableStateOf("doc-${System.currentTimeMillis()}")
    private var statusMessage by mutableStateOf<String?>(null)
    private var screen by mutableStateOf(Screen.LiveFeed)
    private var sourceIsCamera by mutableStateOf(false)

    private var pendingNetworkAction: (() -> Unit)? = null
    // Disables Pause/Resume/Stop while their own request is in flight so a slow
    // network can't invite a duplicate or contradictory tap.
    private var controlActionInFlight by mutableStateOf(false)
    private var rawCaptureBitmap by mutableStateOf<Bitmap?>(null)
    private var suggestedCorners by mutableStateOf<List<Offset>?>(null)

    // Crop corners the user confirmed for the current document (in raw-capture pixels).
    // Re-used by the "scan signed document" button so no new crop is needed.
    private var confirmedCorners: List<Offset>? = null
    private var confirmedRawSize: IntSize? = null
    @Volatile private var pendingSignedScan = false
    @Volatile private var pendingSignAgain = false
    @Volatile private var pendingScanName = "DocSign_SignedScan"
    @Volatile private var pendingScanShare = false
    private var scanInFlight by mutableStateOf(false)

    // "New Document" opens the home screen with the live feed OFF until the user confirms.
    private var liveFeedEnabled by mutableStateOf(true)
    private var askLiveFeed by mutableStateOf(false)

    val onCaptureResultReady: (Bitmap, List<Offset>) -> Unit = { bitmap, corners ->
        if (pendingSignedScan) {
            pendingSignedScan = false
            saveSignedScan(bitmap, corners)
        } else if (pendingSignAgain) {
            pendingSignAgain = false
            signAgainFromCapture(bitmap, corners)
        } else {
            pendingCaptureRequest = false
            rawCaptureBitmap = bitmap
            suggestedCorners = corners
            statusMessage = null
            screen = Screen.Crop
        }
        Unit
    }

    private fun resetToHome() {
        pdfPageBitmap = null
        signedPreviewBitmap = null
        rawCaptureBitmap = null
        suggestedCorners = null
        confirmedCorners = null
        confirmedRawSize = null
        pendingSignedScan = false
        pendingSignAgain = false
        scanInFlight = false
        pendingCaptureRequest = false
        statusMessage = null
        documentId = "doc-${System.currentTimeMillis()}"
        liveFeedEnabled = true
        askLiveFeed = false
        screen = Screen.LiveFeed
    }

    @OptIn(ExperimentalMaterial3Api::class)
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        // White status-bar icons on the blue title bar.
        try {
            WindowCompat.getInsetsController(window, window.decorView)?.isAppearanceLightStatusBars = false
        } catch (e: Exception) { }

        wipeStoredPairCode(applicationContext)
        LiveFeedSession.onPairingRevoked = { runOnUiThread { resetToHome() } }
        LiveFeedSession.start(applicationContext)
        // A fresh launch (not a rotation / state restore) never inherits a code: forget it, stop any session that is
        // still alive in this process and ask again.
        if (savedInstanceState == null) { savePairCode(""); LiveFeedSession.revokePairing(null) }

        if (intent?.action == "android.intent.action.SEND" && intent.type == "application/pdf") {
            val uri = intent.getParcelableExtra<Uri>("android.intent.extra.STREAM")
            uri?.let { loadPdfFirstPage(it) }
        }

        setContent {
            MaterialTheme(
                colorScheme = lightColorScheme(
                    primary = Color(0xFF1E3A8A),
                    onPrimary = Color.White,
                    secondary = Color(0xFF2563EB),
                    surface = Color.White,
                    background = Color(0xFFF3F6FA),
                    surfaceVariant = Color(0xFFEAF0F7),
                    onSurfaceVariant = Color(0xFF52606D)
                )
            ) {
                // No lock button any more: the code is asked for only when there is none (first start) or when the
                // host renewed it. The dialog cannot be dismissed, so nothing can stream until a code is entered.
                if (pairCode.length != PAIR_CODE_LEN) {
                    PairCodeDialog(
                        canDismiss = false,
                        notice = pairNotice,
                        current = pairCode,
                        onSubmit = { code ->
                            savePairCode(code)
                            pairNotice = null
                            LiveFeedSession.applyPairCode()
                        },
                        onDismiss = { }
                    )
                }

                BackHandler(enabled = screen != Screen.LiveFeed) {
                    when (screen) {
                        Screen.PauseConfirm -> Toast.makeText(
                            this@MainActivity,
                            "Machine is paused — tap Resume or Stop job first.",
                            Toast.LENGTH_SHORT
                        ).show()
                        Screen.WatchSigning -> screen = Screen.Doodle
                        Screen.Doodle -> {
                            if (sourceIsCamera) screen = Screen.Crop
                            else resetToHome()
                        }
                        Screen.Crop -> screen = Screen.LiveFeed
                        Screen.LiveFeed -> { }
                    }
                }

                Scaffold(
                    topBar = {
                        Surface(
                            color = MaterialTheme.colorScheme.primary,
                            shadowElevation = 4.dp
                        ) {
                            Row(
                                modifier = Modifier
                                    .fillMaxWidth()
                                    .statusBarsPadding()
                                    .height(44.dp)
                                    .padding(horizontal = 12.dp),
                                verticalAlignment = Alignment.CenterVertically,
                                horizontalArrangement = Arrangement.SpaceBetween
                            ) {
                                Row(verticalAlignment = Alignment.CenterVertically) {
                                    if (screen != Screen.LiveFeed) {
                                        IconButton(onClick = { resetToHome() }) {
                                            Icon(
                                                imageVector = Icons.Default.Home,
                                                contentDescription = "Home",
                                                tint = Color.White
                                            )
                                        }
                                        Spacer(Modifier.width(4.dp))
                                    }
                                    Text(
                                        "DocSign Pro",
                                        fontWeight = FontWeight.Bold,
                                        fontSize = 18.sp,
                                        color = Color.White
                                    )
                                }

                                Row(verticalAlignment = Alignment.CenterVertically) {
                                    if (screen == Screen.Doodle && !sourceIsCamera) {
                                        TextButton(onClick = { resetToHome() }) {
                                            Text("Camera Feed", color = Color.White, fontWeight = FontWeight.SemiBold)
                                        }
                                    }
                                    if (screen == Screen.Doodle && sourceIsCamera && rawCaptureBitmap != null) {
                                        // the auto-crop can be wrong: reopen the crop screen on the same capture to fix the corners
                                        TextButton(onClick = { statusMessage = null; screen = Screen.Crop }) {
                                            Text("Adjust crop", color = Color.White, fontWeight = FontWeight.SemiBold)
                                        }
                                    }
                                }
                            }
                        }
                    },
                    containerColor = MaterialTheme.colorScheme.background
                ) { padding ->
                    Box(modifier = Modifier.padding(padding).fillMaxSize()) {
                        when (screen) {
                            Screen.LiveFeed -> LiveFeedScreen(
                                statusMessage = statusMessage,
                                streamEnabled = liveFeedEnabled,
                                showAsk = askLiveFeed,
                                onStartStream = { liveFeedEnabled = true; askLiveFeed = false },
                                onDismissAsk = { askLiveFeed = false },
                                onCapture = { fetchRawCaptureAndProceedToCrop() },
                                onCaptureResult = onCaptureResultReady
                            )

                            Screen.Crop -> CropScreen(
                                rawBitmap = rawCaptureBitmap,
                                initialCorners = suggestedCorners,
                                statusMessage = statusMessage,
                                onRetake = {
                                    rawCaptureBitmap = null
                                    suggestedCorners = null
                                    statusMessage = null
                                    screen = Screen.LiveFeed
                                },
                                onConfirm = { corners -> confirmCropAndProceed(corners) },
                                onExportPdf = { corners, name, share -> exportCroppedPdf(corners, name, share) }
                            )

                            Screen.Doodle -> DocSignScreen(
                                pageBitmap = pdfPageBitmap,
                                documentId = documentId,
                                statusMessage = statusMessage,
                                onApprove = { rawStrokes, rawWidths, canvasSize, bmpWidth, bmpHeight ->
                                    if (!hostMachineConnected) {
                                        statusMessage = "Machine not connected - live view only. Nothing was sent."
                                        Toast.makeText(
                                            this@MainActivity,
                                            "The plotter machine is not connected to the host PC, so the signature was NOT sent. The live view still works.",
                                            Toast.LENGTH_LONG
                                        ).show()
                                        return@DocSignScreen
                                    }
                                    statusMessage = "Uploading signature to machine..."

                                    val scaleX = bmpWidth.toFloat() / canvasSize.width.toFloat()
                                    val scaleY = bmpHeight.toFloat() / canvasSize.height.toFloat()
                                    val pageSpaceStrokes = rawStrokes.map { stroke ->
                                        stroke.map { p -> Offset(p.x * scaleX, p.y * scaleY) }
                                    }
                                    val widthScale = (scaleX + scaleY) / 2f
                                    val pageSpaceStrokeWidths = rawWidths.map { it * widthScale }

                                    pdfPageBitmap?.let { baseBmp ->
                                        signedPreviewBitmap = renderCompositePreview(
                                            baseBmp,
                                            pageSpaceStrokes,
                                            pageSpaceStrokeWidths
                                        )
                                    }

                                    val actionExecuted = AtomicBoolean(false)
                                    val triggerUpload = {
                                        if (actionExecuted.compareAndSet(false, true)) {
                                            Thread {
                                                try {
                                                    val doodleOnly = renderDoodleOnly(pageSpaceStrokes, pageSpaceStrokeWidths, bmpWidth, bmpHeight)

                                                    val normalizedStrokes = pageSpaceStrokes.map { stroke ->
                                                        stroke.map { p ->
                                                            Offset(
                                                                (p.x / bmpWidth.toFloat()) * ASSUMED_PAGE_WIDTH_PTS,
                                                                (p.y / bmpHeight.toFloat()) * ASSUMED_PAGE_HEIGHT_PTS
                                                            )
                                                        }
                                                    }

                                                    uploadSignedDocument(
                                                        documentId,
                                                        normalizedStrokes,
                                                        doodleOnly,
                                                        ASSUMED_PAGE_WIDTH_PTS,
                                                        ASSUMED_PAGE_HEIGHT_PTS
                                                    )
                                                } catch (e: Exception) {
                                                    e.printStackTrace()
                                                    runOnUiThread { statusMessage = "Thread Error: ${e.message}" }
                                                }
                                            }.start()
                                        }
                                    }

                                    pendingNetworkAction = triggerUpload
                                    Handler(Looper.getMainLooper()).postDelayed({
                                        triggerUpload()
                                    }, 1200)

                                    screen = Screen.WatchSigning
                                }
                            )

                            Screen.WatchSigning -> WatchSigningScreen(
                                statusMessage = statusMessage,
                                signedPreviewBitmap = signedPreviewBitmap,
                                controlsBusy = controlActionInFlight,
                                scanBusy = scanInFlight,
                                onScanSignedPdf = { name, share -> requestSignedScan(name, share) },
                                onPauseRequested = { pauseSigning() },
                                onSignAgain = { requestSignAgainCapture() },
                                onNewDocument = {
                                    resetToHome()
                                    liveFeedEnabled = false   // don't open the feed yet
                                    askLiveFeed = true        // ask first
                                },
                                onCaptureResult = onCaptureResultReady,
                                onStreamLive = {
                                    pendingNetworkAction?.invoke()
                                    pendingNetworkAction = null
                                }
                            )

                            Screen.PauseConfirm -> PauseConfirmScreen(
                                statusMessage = statusMessage,
                                controlsBusy = controlActionInFlight,
                                onContinue = { resumeSigning() },
                                onAbort = { abortSigning() },
                                onCaptureResult = onCaptureResultReady
                            )
                        }
                    }
                }
            }
        }
    }

    override fun onResume() {
        super.onResume()
        LiveFeedSession.cancelBackgroundTimer()
        LiveFeedSession.ensureAlive()
    }

    override fun onPause() {
        super.onPause()
        // Don't tear down instantly - a quick screen-off/app-switch shouldn't drop the stream.
        // But if we're still backgrounded 30 seconds later, stop burning TURN bandwidth.
        LiveFeedSession.scheduleBackgroundSuspend()
    }

    override fun onDestroy() {
        super.onDestroy()
        if (isFinishing) LiveFeedSession.shutdown()
    }

    private fun fetchRawCaptureAndProceedToCrop() {
        val ws = signalingWebSocket
        if (ws != null && isSignalingConnected) {
            statusMessage = "Capturing document..."
            val sent = ws.send(JSONObject().put("type", "capture").toString())
            if (!sent) {
                pendingCaptureRequest = true
                statusMessage = "Reconnecting camera, capturing automatically..."
            }
        } else {
            pendingCaptureRequest = true
            statusMessage = "Camera syncing, capturing automatically..."
        }
    }

    private fun confirmCropAndProceed(corners: List<Offset>) {
        val raw = rawCaptureBitmap ?: return
        statusMessage = "Processing scan..."
        confirmedCorners = corners
        confirmedRawSize = IntSize(raw.width, raw.height)
        Thread {
            try {
                val warped = warpDocument(raw, corners)
                runOnUiThread {
                    pdfPageBitmap = warped
                    sourceIsCamera = true
                    // Keep the raw capture and the user's adjusted corners so the
                    // Back button returns to a working crop page (it used to show
                    // "No capture available").
                    suggestedCorners = corners
                    statusMessage = null
                    screen = Screen.Doodle
                }
            } catch (e: Exception) {
                runOnUiThread { statusMessage = "Crop Error: ${e.message}" }
            }
        }.start()
    }

    // DOWNLOAD #2 — after sending to the plotter: scan the physical (now signed) paper
    // with the host camera, crop it with the SAME corners used before, save as PDF.
    private fun requestSignedScan(name: String, share: Boolean) {
        if (scanInFlight) return
        pendingScanName = name
        pendingScanShare = share
        val ws = signalingWebSocket
        if (ws == null || !isSignalingConnected) {
            Toast.makeText(this, "Camera is not connected yet — try again in a moment.", Toast.LENGTH_SHORT).show()
            return
        }
        pendingSignedScan = true
        scanInFlight = true
        statusMessage = "Scanning signed document..."
        val sent = ws.send(JSONObject().put("type", "capture").toString())
        if (!sent) {
            pendingSignedScan = false
            scanInFlight = false
            statusMessage = "Could not reach the camera. Try again."
            return
        }
        Handler(Looper.getMainLooper()).postDelayed({
            if (pendingSignedScan) {
                pendingSignedScan = false
                scanInFlight = false
                statusMessage = "Scan timed out — try again."
            }
        }, 20000L)
    }

    // SIGN AGAIN - the paper now carries the first signature, so take a fresh picture of it, crop it
    // automatically and use THAT as the page to sign on (not the old, unsigned one).
    private fun requestSignAgainCapture() {
        if (scanInFlight) return
        val ws = signalingWebSocket
        if (ws == null || !isSignalingConnected) {
            Toast.makeText(this, "Camera is not connected yet — try again in a moment.", Toast.LENGTH_SHORT).show()
            return
        }
        pendingSignAgain = true
        scanInFlight = true
        statusMessage = "Capturing the signed page..."
        val sent = ws.send(JSONObject().put("type", "capture").toString())
        if (!sent) {
            pendingSignAgain = false
            scanInFlight = false
            statusMessage = "Could not reach the camera. Try again."
            return
        }
        Handler(Looper.getMainLooper()).postDelayed({
            if (pendingSignAgain) {
                pendingSignAgain = false
                scanInFlight = false
                statusMessage = "Capture timed out — try Sign Again once more."
            }
        }, 20000L)
    }

    private fun signAgainFromCapture(capture: Bitmap, autoCorners: List<Offset>) {
        statusMessage = "Cropping the signed page..."
        Thread {
            try {
                // Re-use the crop corners the user already confirmed for this document (scaled to this capture),
                // exactly like the signed-scan PDF does - the paper has not moved. Auto-detected corners are only
                // the fallback when no corners were ever saved.
                val saved = confirmedCorners
                val savedSize = confirmedRawSize
                val haveSaved = saved != null && saved.size == 4 && savedSize != null &&
                        savedSize.width > 0 && savedSize.height > 0
                val useCorners = if (haveSaved) {
                    val sx = capture.width.toFloat() / savedSize!!.width.toFloat()
                    val sy = capture.height.toFloat() / savedSize.height.toFloat()
                    saved!!.map { Offset(it.x * sx, it.y * sy) }
                } else autoCorners
                if (!haveSaved && !lastCaptureDetected) {
                    // Page edges not found: let the user place the corners instead of signing on a bad crop.
                    runOnUiThread {
                        rawCaptureBitmap = capture
                        suggestedCorners = useCorners
                        documentId = "doc-${System.currentTimeMillis()}"
                        signedPreviewBitmap = null
                        scanInFlight = false
                        statusMessage = "Could not find the page edges - please adjust the corners."
                        screen = Screen.Crop
                    }
                    return@Thread
                }
                val warped = warpDocument(capture, useCorners)
                runOnUiThread {
                    rawCaptureBitmap = capture
                    suggestedCorners = useCorners
                    confirmedCorners = useCorners
                    confirmedRawSize = IntSize(capture.width, capture.height)
                    pdfPageBitmap = warped
                    sourceIsCamera = true
                    documentId = "doc-${System.currentTimeMillis()}"
                    signedPreviewBitmap = null
                    scanInFlight = false
                    statusMessage = null
                    screen = Screen.Doodle
                }
            } catch (e: Exception) {
                runOnUiThread {
                    scanInFlight = false
                    statusMessage = "Could not crop the signed page: ${e.message}"
                }
            }
        }.start()
    }

    private fun saveSignedScan(capture: Bitmap, autoCorners: List<Offset>) {
        scanInFlight = true
        statusMessage = "Saving signed scan..."
        Thread {
            try {
                val saved = confirmedCorners
                val savedSize = confirmedRawSize
                val useCorners = if (saved != null && saved.size == 4 && savedSize != null &&
                    savedSize.width > 0 && savedSize.height > 0
                ) {
                    val sx = capture.width.toFloat() / savedSize.width.toFloat()
                    val sy = capture.height.toFloat() / savedSize.height.toFloat()
                    saved.map { Offset(it.x * sx, it.y * sy) }
                } else autoCorners
                val warped = warpDocument(capture, useCorners)
                val name = pendingScanName
                val share = pendingScanShare
                val saved2 = if (share) null else saveBitmapAsPdf(applicationContext, warped, name)
                runOnUiThread {
                    val res = if (share) shareBitmapAsPdf(this, warped, name) else saved2
                    scanInFlight = false
                    statusMessage = res ?: "Failed to export PDF"
                    Toast.makeText(this, res ?: "Failed to export PDF", Toast.LENGTH_LONG).show()
                }
            } catch (e: Exception) {
                runOnUiThread {
                    scanInFlight = false
                    statusMessage = "Scan error: ${e.message}"
                }
            }
        }.start()
    }

    // PDF #1 — cropped scan, saved to Downloads or shared (name chosen by the user in a popup).
    private fun exportCroppedPdf(corners: List<Offset>, name: String, share: Boolean) {
        val raw = rawCaptureBitmap ?: return
        Toast.makeText(this, "Preparing PDF...", Toast.LENGTH_SHORT).show()
        Thread {
            try {
                val warped = warpDocument(raw, corners)
                val saved = if (share) null else saveBitmapAsPdf(applicationContext, warped, name)
                runOnUiThread {
                    val res = if (share) shareBitmapAsPdf(this, warped, name) else saved
                    Toast.makeText(this, res ?: "Failed to export PDF", Toast.LENGTH_LONG).show()
                }
            } catch (e: Exception) {
                runOnUiThread { Toast.makeText(this, "PDF error: ${e.message}", Toast.LENGTH_LONG).show() }
            }
        }.start()
    }

    private fun pauseSigning() {
        if (controlActionInFlight) return
        controlActionInFlight = true
        statusMessage = "Pausing machine..."
        screen = Screen.PauseConfirm
        Thread {
            try {
                val client = OkHttpClient()
                val request = Request.Builder()
                    .url("$BACKEND_BASE_URL/api/documents/$documentId/pause?code=${pairKey()}")
                    .post("".toRequestBody(null))
                    .build()
                client.newCall(request).execute().use { response ->
                    val bodyStr = try { response.body?.string() } catch (e: Exception) { null }
                    runOnUiThread {
                        controlActionInFlight = false
                        statusMessage = if (response.isSuccessful) null
                        else "Pause failed: server returned ${response.code}${if (bodyStr != null) " — $bodyStr" else ""}"
                    }
                }
            } catch (e: Exception) {
                runOnUiThread {
                    controlActionInFlight = false
                    statusMessage = "Pause error: ${e.message}"
                }
            }
        }.start()
    }

    private fun resumeSigning() {
        if (controlActionInFlight) return
        controlActionInFlight = true
        statusMessage = "Resuming machine..."
        val actionExecuted = AtomicBoolean(false)
        val triggerResume = {
            if (actionExecuted.compareAndSet(false, true)) {
                Thread {
                    try {
                        val client = OkHttpClient()
                        val request = Request.Builder()
                            .url("$BACKEND_BASE_URL/api/documents/$documentId/resume?code=${pairKey()}")
                            .post("".toRequestBody(null))
                            .build()
                        client.newCall(request).execute().use { response ->
                            val bodyStr = try { response.body?.string() } catch (e: Exception) { null }
                            runOnUiThread {
                                controlActionInFlight = false
                                statusMessage = if (response.isSuccessful) null
                                else "Resume failed: server returned ${response.code}${if (bodyStr != null) " — $bodyStr" else ""}"
                            }
                        }
                    } catch (e: Exception) {
                        runOnUiThread {
                            controlActionInFlight = false
                            statusMessage = "Resume error: ${e.message}"
                        }
                    }
                }.start()
            }
        }
        pendingNetworkAction = triggerResume
        Handler(Looper.getMainLooper()).postDelayed({ triggerResume() }, 1200)
        screen = Screen.WatchSigning
    }

    private fun abortSigning() {
        if (controlActionInFlight) return
        controlActionInFlight = true
        statusMessage = "Stop requested — returning to origin..."
        screen = Screen.WatchSigning
        Thread {
            try {
                val client = OkHttpClient()
                val request = Request.Builder()
                    .url("$BACKEND_BASE_URL/api/documents/$documentId/cancel?code=${pairKey()}")
                    .post("".toRequestBody(null))
                    .build()
                client.newCall(request).execute().use { response ->
                    val bodyStr = try { response.body?.string() } catch (e: Exception) { null }
                    runOnUiThread {
                        controlActionInFlight = false
                        statusMessage = if (response.isSuccessful) "Stop requested. The host will return to origin."
                        else "Abort failed: server returned ${response.code}${if (bodyStr != null) " — $bodyStr" else ""}"
                    }
                }
            } catch (e: Exception) {
                runOnUiThread {
                    controlActionInFlight = false
                    statusMessage = "Abort error: ${e.message}"
                }
            }
        }.start()
    }

    private fun loadPdfFirstPage(uri: Uri) {
        statusMessage = "Opening document..."
        Thread {
            try {
                var result: Bitmap? = null
                contentResolver.openFileDescriptor(uri, "r")?.use { pfd: ParcelFileDescriptor ->
                    PdfRenderer(pfd).use { renderer ->
                        val page = renderer.openPage(0)
                        val bitmap = Bitmap.createBitmap(page.width, page.height, Bitmap.Config.ARGB_8888)
                        page.render(bitmap, null, null, PdfRenderer.Page.RENDER_MODE_FOR_DISPLAY)
                        page.close()
                        result = bitmap
                    }
                }
                runOnUiThread {
                    result?.let {
                        pdfPageBitmap = it
                        sourceIsCamera = false
                        confirmedCorners = null
                        confirmedRawSize = null
                        statusMessage = null
                        screen = Screen.Doodle
                    }
                }
            } catch (e: Exception) {
                runOnUiThread { statusMessage = "PDF Error: ${e.message}" }
            }
        }.start()
    }

    private fun uploadSignedDocument(
        docId: String,
        strokes: List<List<Offset>>,
        doodleImage: Bitmap,
        pageWidth: Int,
        pageHeight: Int
    ) {
        try {
            val strokesJson = strokesToJson(strokes)
            val imageFile = File(cacheDir, "$docId-doodle.png")
            imageFile.outputStream().use { out ->
                doodleImage.compress(Bitmap.CompressFormat.PNG, 100, out)
            }

            val client = OkHttpClient()
            val body = MultipartBody.Builder()
                .setType(MultipartBody.FORM)
                .addFormDataPart("documentId", docId)
                .addFormDataPart("pairCode", pairKey())
                .addFormDataPart("strokes", strokesJson)
                .addFormDataPart("pageWidthPts", pageWidth.toString())
                .addFormDataPart("pageHeightPts", pageHeight.toString())
                .addFormDataPart(
                    "doodleImage", imageFile.name,
                    imageFile.asRequestBody("image/png".toMediaType())
                )
                .build()

            val request = Request.Builder()
                .url(BACKEND_UPLOAD_URL)
                .post(body)
                .build()

            client.newCall(request).execute().use { response ->
                runOnUiThread {
                    if (response.isSuccessful) {
                        statusMessage = "Uploaded — machine is signing now"
                    } else {
                        statusMessage = "Upload failed: server returned ${response.code}"
                    }
                }
            }
        } catch (e: Exception) {
            e.printStackTrace()
            runOnUiThread {
                statusMessage = "Network Error: ${e.javaClass.simpleName} — ${e.message}"
            }
        }
    }

    private fun strokesToJson(strokes: List<List<Offset>>): String {
        val sb = StringBuilder("[")
        strokes.forEachIndexed { i, stroke ->
            sb.append("[")
            stroke.forEachIndexed { j, p ->
                sb.append("{\"x\":${p.x},\"y\":${p.y}}")
                if (j != stroke.lastIndex) sb.append(",")
            }
            sb.append("]")
            if (i != strokes.lastIndex) sb.append(",")
        }
        sb.append("]")
        return sb.toString()
    }
}

private object LiveFeedSession {
    private val mainHandler = Handler(Looper.getMainLooper())
    private var started = false
    private var appContext: android.content.Context? = null
    private var eglBase: EglBase? = null
    private var factory: PeerConnectionFactory? = null
    private var client: OkHttpClient? = null
    private var peerConnection: PeerConnection? = null
    private var socket: WebSocket? = null
    private var videoTrack: VideoTrack? = null

    @Volatile private var generation = 0
    @Volatile private var firstFrameSeen = false
    @Volatile private var lastFrameAt = 0L
    private var reconnectDelayMs = 1500L
    @Volatile private var answerReceived = false
    @Volatile private var answerReceivedAt = 0L
    @Volatile private var offerInFlight = false
    @Volatile private var lastOfferSdp: String? = null
    @Volatile private var connectStartedAt = 0L
    private var restartPending = false
    private var hostThrottled = false
    private var retryRunnable: Runnable? = null
    private var backgroundRunnable: Runnable? = null
    @Volatile private var suspendedForBackground = false
    private const val BACKGROUND_TIMEOUT_MS = 0L

    private val sinks = CopyOnWriteArrayList<VideoSink>()
    // Every local ICE candidate of the CURRENT peer connection. They are re-sent together with
    // every re-sent offer, so a host that (re)connects late still receives them.
    private val localCandidates = CopyOnWriteArrayList<IceCandidate>()

    val qualityLevels = listOf("Low (480p)", "Medium (1080p)", "High (Max)")
    /** The phone owns the live-feed quality; the host starts on Medium and is told this on every (re)connect. */
    var streamQuality by mutableStateOf("Medium (1080p)")

    // ---- Zoom region: while zoomed in, the host sends only the visible part of the camera frame at full detail ----
    /** Region the frames on screen are currently cut to (null = whole frame). Set only after the host confirms. */
    var activeRoi by mutableStateOf<ZoomRoi?>(null)
    /** Region we last asked the host for. */
    @Volatile var requestedRoi: ZoomRoi? = null
    @Volatile private var roiSeq = 0
    @Volatile private var roiPendingSeq = 0
    /** Aspect ratio (w/h) of the incoming video, reported by the renderer. */
    var videoAspect by mutableStateOf(0.75f)

    fun requestRoi(roi: ZoomRoi?) {
        requestedRoi = roi
        val ws = socket ?: return
        if (!isSignalingConnected) return
        roiSeq++
        roiPendingSeq = roiSeq
        try {
            ws.send(
                JSONObject().put("type", "roi").put("seq", roiSeq)
                    .put("x", (roi?.x ?: 0f).toDouble())
                    .put("y", (roi?.y ?: 0f).toDouble())
                    .put("s", (roi?.sx ?: 1f).toDouble())
                    .toString()
            )
        } catch (e: Exception) {}
    }

    fun resetRoi() {
        requestedRoi = null
        mainHandler.post { activeRoi = null }
    }

    fun updateStreamQuality(level: String) {
        streamQuality = level
        sendQualityToHost()
    }

    fun sendQualityToHost() {
        val ws = socket
        if (ws != null && isSignalingConnected) {
            ws.send(JSONObject().put("type", "quality").put("level", streamQuality).toString())
        }
    }

    var statusMessage by mutableStateOf("Connecting...")
        private set
    var progress by mutableStateOf(0f)
        private set

    @Volatile var captureCallback: ((Bitmap, List<Offset>) -> Unit)? = null

    val eglContext: EglBase.Context? get() = eglBase?.eglBaseContext

    /** True while decoded video frames are really arriving (used to self-heal a black renderer). */
    fun isReceivingFrames(): Boolean =
        firstFrameSeen && android.os.SystemClock.elapsedRealtime() - lastFrameAt < 2500L

    private fun attachRemoteVideo(track: VideoTrack) {
        if (videoTrack === track) return
        try { videoTrack?.removeSink(masterSink) } catch (e: Exception) {}
        videoTrack = track
        try { track.setEnabled(true) } catch (e: Exception) {}
        track.addSink(masterSink)
    }

    private fun setStatus(message: String, p: Float) {
        statusMessage = message
        if (p > progress || p == 0.25f || p == 0f) progress = p
    }

    private fun status(message: String, p: Float) {
        mainHandler.post { setStatus(message, p) }
    }

    private val masterSink = VideoSink { frame ->
        lastFrameAt = android.os.SystemClock.elapsedRealtime()
        if (!firstFrameSeen) {
            firstFrameSeen = true
            mainHandler.post {
                reconnectDelayMs = 1500L
                setStatus("Connected", 1.0f)
                sendQualityToHost()
                if (pendingCaptureRequest) {
                    pendingCaptureRequest = false
                    socket?.send(JSONObject().put("type", "capture").toString())
                }
            }
        }
        for (s in sinks) s.onFrame(frame)
    }

    private val watchdog = object : Runnable {
        override fun run() {
            if (!started) return
            if (suspendedForBackground) { mainHandler.postDelayed(this, 4000L); return }
            val now = android.os.SystemClock.elapsedRealtime()
            if (firstFrameSeen && now - lastFrameAt > 8000L) {
                restart("Video stalled. Reconnecting...")
            } else if (!firstFrameSeen && answerReceived && answerReceivedAt > 0L && now - answerReceivedAt > 14000L) {
                // The host answered but no video arrived: this network path (STUN/TURN) did not work.
                // A fresh connection makes the host try its next network profile.
                restart("Trying another network route...")
            } else if (!firstFrameSeen && connectStartedAt > 0L && now - connectStartedAt > 25000L) {
                restart("Retrying connection...")
            }
            mainHandler.postDelayed(this, 4000L)
        }
    }

    fun start(context: android.content.Context) {
        synchronized(this) {
            if (started) return
            started = true
        }
        streamQuality = "Medium (1080p)"
        val app = context.applicationContext
        appContext = app
        PeerConnectionFactory.initialize(
            PeerConnectionFactory.InitializationOptions.builder(app).createInitializationOptions()
        )
        val egl = EglBase.create()
        eglBase = egl
        factory = PeerConnectionFactory.builder()
            .setVideoEncoderFactory(DefaultVideoEncoderFactory(egl.eglBaseContext, true, true))
            .setVideoDecoderFactory(DefaultVideoDecoderFactory(egl.eglBaseContext))
            .createPeerConnectionFactory()
        client = OkHttpClient.Builder()
            .pingInterval(20, TimeUnit.SECONDS)
            .connectTimeout(30, TimeUnit.SECONDS)
            .build()
        // Wake a sleeping (free-tier) backend; harmless if it is already awake.
        Thread {
            try {
                OkHttpClient.Builder().callTimeout(70, TimeUnit.SECONDS).build()
                    .newCall(Request.Builder().url(BACKEND_BASE_URL).build()).execute().close()
            } catch (e: Exception) { }
        }.start()
        connect()
        mainHandler.postDelayed(watchdog, 4000L)

        // Re-connect straight away when the phone switches Wi-Fi <-> mobile data.
        try {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
                val cm = app.getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
                cm.registerDefaultNetworkCallback(object : ConnectivityManager.NetworkCallback() {
                    override fun onAvailable(network: Network) {
                        mainHandler.post {
                            val now = android.os.SystemClock.elapsedRealtime()
                            val receiving = firstFrameSeen && now - lastFrameAt < 3000L
                            if (started && !suspendedForBackground && !receiving && now - connectStartedAt > 4000L) {
                                reconnectDelayMs = 1000L
                                restart("Network changed. Reconnecting...")
                            }
                        }
                    }
                })
            }
        } catch (e: Exception) { }
    }

    /** Called when the app comes back to the foreground: revive a dead connection quickly. */
    fun ensureAlive() {
        if (!started) return
        if (suspendedForBackground) {
            suspendedForBackground = false
            streamQuality = "Medium (1080p)"   // a new viewing session always starts on Medium
            reconnectDelayMs = 0L
            restart("Resuming live feed...")
            return
        }
        val now = android.os.SystemClock.elapsedRealtime()
        val stalled = firstFrameSeen && now - lastFrameAt > 5000L
        val neverConnected = !firstFrameSeen && connectStartedAt > 0L && now - connectStartedAt > 10000L
        if (stalled || neverConnected) {
            reconnectDelayMs = 1000L
            restart("Reconnecting...")
        }
    }

    /** Called from onPause(): if the app is still backgrounded BACKGROUND_TIMEOUT_MS later,
     *  fully close the WebRTC connection so it stops consuming metered TURN relay data. */
    fun scheduleBackgroundSuspend() {
        if (!started) return
        cancelBackgroundTimer()
        if (BACKGROUND_TIMEOUT_MS <= 0L) {
            suspendForBackground()
        } else {
            val r = Runnable { suspendForBackground() }
            backgroundRunnable = r
            mainHandler.postDelayed(r, BACKGROUND_TIMEOUT_MS)
        }
    }

    fun cancelBackgroundTimer() {
        backgroundRunnable?.let { mainHandler.removeCallbacks(it) }
        backgroundRunnable = null
    }

    private fun suspendForBackground() {
        backgroundRunnable = null
        if (!started || suspendedForBackground) return
        suspendedForBackground = true
        resetRoi()
        // Tell the host to stop encoding right away; OkHttp flushes this before closing the socket.
        try { socket?.send(JSONObject().put("type", "stream_control").put("paused", true).toString()) } catch (e: Exception) {}
        generation++                      // old socket/peer callbacks are now ignored
        restartPending = false
        isSignalingConnected = false
        signalingWebSocket = null
        closeCurrent()
        firstFrameSeen = false
        status("Paused - app is in background", 0f)
    }

    fun shutdown() {
        synchronized(this) {
            if (!started) return
            started = false
        }
        generation++
        mainHandler.removeCallbacks(watchdog)
        closeCurrent()
        try { factory?.dispose() } catch (e: Exception) {}
        try { eglBase?.release() } catch (e: Exception) {}
        factory = null
        eglBase = null
        isSignalingConnected = false
        signalingWebSocket = null
        progress = 0f
        statusMessage = "Connecting..."
    }

    fun attach(sink: VideoSink) {
        sinks.add(sink)
        if (hostThrottled) {
            sendControl(false)
            hostThrottled = false
        }
    }

    fun detach(sink: VideoSink) {
        sinks.remove(sink)
        mainHandler.postDelayed({
            if (started && sinks.isEmpty() && !hostThrottled && isSignalingConnected) {
                sendControl(true)
                hostThrottled = true
            }
        }, 800L)
    }

    private fun sendControl(paused: Boolean) {
        val ws = socket
        if (ws != null && isSignalingConnected) {
            ws.send(JSONObject().put("type", "stream_control").put("paused", paused).toString())
        }
    }

    private fun closeCurrent() {
        retryRunnable?.let { mainHandler.removeCallbacks(it) }
        retryRunnable = null
        try { videoTrack?.removeSink(masterSink) } catch (e: Exception) {}
        videoTrack = null
        try { socket?.close(1000, "restart") } catch (e: Exception) {}
        try { peerConnection?.close(); peerConnection?.dispose() } catch (e: Exception) {}
        peerConnection = null
        socket = null
    }

    private fun restart(reason: String) {
        if (!started || restartPending) return
        restartPending = true
        setStatus(reason, 0f)
        val gen = generation
        mainHandler.postDelayed({
            if (started && gen == generation) connect()
        }, reconnectDelayMs)
        reconnectDelayMs = (reconnectDelayMs * 2).coerceAtMost(5000L)
    }

    /** Invoked (on the main thread) after the pairing was revoked, so the UI can drop any half-finished document. */
    var onPairingRevoked: (() -> Unit)? = null

    /**
     * The host renewed its code (or the relay says our code is dead): stop EVERYTHING that depends on the old code -
     * video, signalling socket, reconnect timers - forget the code and make the app ask for the new one.
     */
    fun revokePairing(notice: String? = "The host PC renewed its pairing code. Enter the new code to continue.") {
        mainHandler.post {
            generation++                      // every callback of the old socket / peer is ignored from now on
            restartPending = false
            reconnectDelayMs = 0L
            connectStartedAt = 0L             // watchdog stays alive but has nothing to retry until a new code is entered
            closeCurrent()
            firstFrameSeen = false
            answerReceived = false
            answerReceivedAt = 0L
            offerInFlight = false
            lastOfferSdp = null
            localCandidates.clear()
            isSignalingConnected = false
            signalingWebSocket = null
            hostMachineConnected = false
            resetRoi()
            progress = 0f
            statusMessage = "Enter the pairing code"
            savePairCode("")
            pairNotice = notice
            onPairingRevoked?.invoke()
        }
    }

    /** Called after the user types a (new) pairing code: drop the old connection and connect to that code's room. */
    fun applyPairCode() {
        if (!started) return
        mainHandler.post {
            generation++
            restartPending = false
            closeCurrent()
            firstFrameSeen = false
            reconnectDelayMs = 0L
            connect()
        }
    }

    private fun connect() {
        if (pairCode.length != PAIR_CODE_LEN) {
            restartPending = false
            setStatus("Enter the pairing code from the host PC", 0f)
            return
        }
        val f = factory ?: return
        val gen = ++generation
        restartPending = false
        closeCurrent()
        firstFrameSeen = false
        answerReceived = false
        answerReceivedAt = 0L
        offerInFlight = false
        // STUCK-ON-"Contacting Host" FIX: the offer belongs to ONE PeerConnection.
        // It used to survive here, so after any reconnect (watchdog, socket drop,
        // retry) sendOffer() re-sent the OLD offer while the NEW PeerConnection
        // never created its own — the host's answer then could not be applied
        // and the feed stayed stuck until the app was restarted.
        lastOfferSdp = null
        localCandidates.clear()
        connectStartedAt = android.os.SystemClock.elapsedRealtime()
        isSignalingConnected = false

        val iceServers = listOf(
            // Several independent STUN servers: if one is blocked on this network another still answers.
            PeerConnection.IceServer.builder(
                listOf(
                    "stun:stun.l.google.com:19302",
                    "stun:stun1.l.google.com:19302",
                    "stun:stun.cloudflare.com:3478",
                    "stun:stun.relay.metered.ca:80"
                )
            ).createIceServer(),
            PeerConnection.IceServer.builder(
                listOf(
                    "turn:standard.relay.metered.ca:80",
                    "turn:standard.relay.metered.ca:80?transport=tcp",
                    "turn:standard.relay.metered.ca:443",
                    "turns:standard.relay.metered.ca:443?transport=tcp"
                )
            )
                .setUsername("TURN_USERNAME")
                .setPassword("TURN_PASSWORD")
                .createIceServer()
        )
        val rtcConfig = PeerConnection.RTCConfiguration(iceServers).apply {
            // Keep gathering when the phone switches Wi-Fi <-> mobile data, and allow TCP routes.
            continualGatheringPolicy = PeerConnection.ContinualGatheringPolicy.GATHER_CONTINUALLY
            tcpCandidatePolicy = PeerConnection.TcpCandidatePolicy.ENABLED
        }

        peerConnection = f.createPeerConnection(rtcConfig, object : PeerConnection.Observer {
            override fun onAddStream(stream: MediaStream?) {
                if (gen != generation) return
                val track = stream?.videoTracks?.firstOrNull() ?: return
                attachRemoteVideo(track)
            }

            // Unified-plan builds deliver the video through onTrack instead of onAddStream:
            // listening to both makes sure the video is always attached (never a black screen).
            override fun onTrack(transceiver: RtpTransceiver?) {
                if (gen != generation) return
                val track = transceiver?.receiver?.track() as? VideoTrack ?: return
                mainHandler.post { if (gen == generation) attachRemoteVideo(track) }
            }

            override fun onIceCandidate(candidate: IceCandidate?) {
                if (gen != generation) return
                candidate?.let {
                    localCandidates.add(it)
                    val json = JSONObject()
                    json.put("type", "candidate")
                    json.put("sdpMid", it.sdpMid)
                    json.put("sdpMLineIndex", it.sdpMLineIndex)
                    json.put("candidate", it.sdp)
                    socket?.send(json.toString())
                }
            }

            override fun onIceConnectionChange(state: PeerConnection.IceConnectionState?) {
                if (gen != generation) return
                when (state) {
                    PeerConnection.IceConnectionState.FAILED ->
                        mainHandler.post { if (gen == generation) restart("Connection lost. Reconnecting...") }
                    PeerConnection.IceConnectionState.DISCONNECTED ->
                        mainHandler.postDelayed({
                            if (gen == generation) {
                                val s = peerConnection?.iceConnectionState()
                                if (s != PeerConnection.IceConnectionState.CONNECTED &&
                                    s != PeerConnection.IceConnectionState.COMPLETED
                                ) restart("Connection lost. Reconnecting...")
                            }
                        }, 6000L)
                    else -> {}
                }
            }

            override fun onIceCandidatesRemoved(candidates: Array<out IceCandidate>?) {}
            override fun onSignalingChange(state: PeerConnection.SignalingState?) {}
            override fun onIceConnectionReceivingChange(receiving: Boolean) {}
            override fun onIceGatheringChange(state: PeerConnection.IceGatheringState?) {}
            override fun onRemoveStream(stream: MediaStream?) {}
            override fun onDataChannel(channel: DataChannel?) {}
            override fun onRenegotiationNeeded() {}
        })

        val request = Request.Builder().url("$BACKEND_WEBSOCKET_URL?code=${pairKey()}&role=phone").build()
        val ws = client!!.newWebSocket(request, socketListener(gen))
        socket = ws
        signalingWebSocket = ws
    }

    private fun sendOffer(gen: Int) {
        val existing = lastOfferSdp
        if (existing != null) {
            socket?.send(JSONObject().put("type", "offer").put("sdp", existing).toString())
            for (c in localCandidates) {
                socket?.send(
                    JSONObject()
                        .put("type", "candidate")
                        .put("sdpMid", c.sdpMid)
                        .put("sdpMLineIndex", c.sdpMLineIndex)
                        .put("candidate", c.sdp)
                        .toString()
                )
            }
            return
        }
        if (offerInFlight) return
        offerInFlight = true
        peerConnection?.createOffer(object : SdpObserver {
            override fun onCreateSuccess(desc: SessionDescription?) {
                offerInFlight = false
                if (gen != generation) return
                lastOfferSdp = desc?.description
                peerConnection?.setLocalDescription(this, desc)
                socket?.send(JSONObject().put("type", "offer").put("sdp", desc?.description).toString())
                status("Sending request...", 0.50f)
            }
            override fun onSetSuccess() {}
            override fun onCreateFailure(error: String?) { offerInFlight = false }
            override fun onSetFailure(error: String?) {}
        }, MediaConstraints())
    }

    private fun socketListener(gen: Int) = object : WebSocketListener() {
        override fun onOpen(webSocket: WebSocket, response: Response) {
            if (gen != generation) return
            signalingWebSocket = webSocket
            isSignalingConnected = true
            answerReceived = false
            status("Contacting Host...", 0.25f)

            peerConnection?.addTransceiver(
                MediaStreamTrack.MediaType.MEDIA_TYPE_VIDEO,
                RtpTransceiver.RtpTransceiverInit(RtpTransceiver.RtpTransceiverDirection.RECV_ONLY)
            )
            sendOffer(gen)

            hostThrottled = false
            webSocket.send(JSONObject().put("type", "stream_control").put("paused", false).toString())
            resetRoi()

            val retry = object : Runnable {
                override fun run() {
                    if (gen == generation && isSignalingConnected && !answerReceived) {
                        status("Host PC not connected. Retrying...", 0.25f)
                        sendOffer(gen)
                        mainHandler.postDelayed(this, 3000L)
                    }
                }
            }
            retryRunnable = retry
            mainHandler.postDelayed(retry, 4000L)

            if (pendingCaptureRequest) {
                pendingCaptureRequest = false
                webSocket.send(JSONObject().put("type", "capture").toString())
            }
        }

        override fun onMessage(webSocket: WebSocket, text: String) {
            if (gen != generation) return
            try {
                val json = JSONObject(text)
                when (json.optString("type")) {
                    "host_ready", "host_status" -> {
                        // The host reports whether its plotter machine is connected.
                        if (json.has("machine")) hostMachineConnected = json.optBoolean("machine", true)
                        // host_ready: the host PC just (re)connected to the server. If we are still
                        // waiting for an answer, offer again right now instead of at the next retry tick.
                        if (json.optString("type") == "host_ready" && !answerReceived) {
                            mainHandler.post { if (gen == generation) sendOffer(gen) }
                        }
                    }
                    "answer" -> {
                        // Ignore duplicate answers (the host re-sends its answer when it
                        // sees a repeated offer) — only apply one that matches our offer.
                        if (answerReceived ||
                            peerConnection?.signalingState() != PeerConnection.SignalingState.HAVE_LOCAL_OFFER
                        ) return
                        answerReceived = true
                        answerReceivedAt = android.os.SystemClock.elapsedRealtime()
                        retryRunnable?.let { mainHandler.removeCallbacks(it) }
                        peerConnection?.setRemoteDescription(
                            object : SdpObserver {
                                override fun onCreateSuccess(p0: SessionDescription?) {}
                                override fun onSetSuccess() {}
                                override fun onCreateFailure(p0: String?) {}
                                override fun onSetFailure(p0: String?) {}
                            },
                            SessionDescription(SessionDescription.Type.ANSWER, json.getString("sdp"))
                        )
                        status("Loading Video Stream...", 0.75f)
                    }
                    "room" -> {
                        if (!json.optBoolean("host", true)) status("Host PC not online for this code. Check the code...", 0.1f)
                    }
                    "code_renewed" -> revokePairing()      // host made a new code: stop all streaming, ask for the new one
                    "roi_applied" -> {
                        val seq = json.optInt("seq", -1)
                        if (seq == roiPendingSeq) {
                            // The host confirms the EXACT (pixel-rounded) region and says a frame with it was just sent.
                            val sx = json.optDouble("sx", 1.0).toFloat()
                            val sy = json.optDouble("sy", 1.0).toFloat()
                            val roi = if (sx < 0.98f) ZoomRoi(json.optDouble("x", 0.0).toFloat(), json.optDouble("y", 0.0).toFloat(), sx, sy) else null
                            // short wait for network + decode of that frame, so the switch happens exactly when it appears
                            mainHandler.postDelayed({ if (gen == generation && seq == roiPendingSeq) activeRoi = roi }, 450L)
                        }
                    }
                    "candidate" -> {
                        val candidate = IceCandidate(
                            json.getString("sdpMid"),
                            json.getInt("sdpMLineIndex"),
                            json.getString("candidate")
                        )
                        peerConnection?.addIceCandidate(candidate)
                    }
                    "capture_result" -> {
                        val imageBytes = android.util.Base64.decode(json.getString("image"), android.util.Base64.DEFAULT)
                        val bitmap = android.graphics.BitmapFactory.decodeByteArray(imageBytes, 0, imageBytes.size)
                        val corners = json.getString("corners").split(",").map { it.toFloat() }
                            .chunked(2).map { (x, y) -> Offset(x, y) }
                        lastCaptureDetected = json.optBoolean("detected", true)
                        if (bitmap != null) {
                            mainHandler.post { captureCallback?.invoke(bitmap, corners) }
                        }
                    }
                }
            } catch (e: Exception) {
            }
        }

        override fun onClosing(webSocket: WebSocket, code: Int, reason: String) {
            // 4403 = the relay says this code was renewed by the host (also covers a phone that was offline at the time)
            if (gen == generation && code == 4403) revokePairing()
        }

        override fun onClosed(webSocket: WebSocket, code: Int, reason: String) {
            if (gen != generation) return
            if (code == 4403) { revokePairing(); return }
            isSignalingConnected = false
            retryRunnable?.let { mainHandler.removeCallbacks(it) }
            mainHandler.post { if (gen == generation) restart("Connection lost. Reconnecting...") }
        }

        override fun onFailure(webSocket: WebSocket, t: Throwable, response: Response?) {
            if (gen != generation) return
            isSignalingConnected = false
            retryRunnable?.let { mainHandler.removeCallbacks(it) }
            mainHandler.post { if (gen == generation) restart("Connection lost. Reconnecting...") }
        }
    }
}

/**
 * Video renderer on a TextureView. Unlike SurfaceView it lives in the normal view hierarchy,
 * so Compose can scale / translate it every frame without the lag and tearing a SurfaceView
 * shows while zooming and panning.
 */
private class DocTextureRenderer(context: Context) : TextureView(context), VideoSink, TextureView.SurfaceTextureListener {
    private val eglRenderer = EglRenderer("DocSignTextureRenderer")
    private var initialized = false
    private var surfaceReady = false
    private var lastW = 0
    private var lastH = 0
    var onAspect: ((Float) -> Unit)? = null
    val isSurfaceReady: Boolean get() = initialized && surfaceReady

    init {
        surfaceTextureListener = this
        isOpaque = true
    }

    fun setup(sharedContext: EglBase.Context?) {
        if (initialized) return
        eglRenderer.init(sharedContext, EglBase.CONFIG_PLAIN, GlRectDrawer())
        initialized = true
        val st = surfaceTexture
        if (isAvailable && st != null && !surfaceReady) {
            eglRenderer.createEglSurface(st)
            surfaceReady = true
        }
    }

    fun releaseRenderer() {
        if (!initialized) return
        initialized = false
        surfaceReady = false
        try { eglRenderer.release() } catch (e: Exception) { }
    }

    override fun onFrame(frame: VideoFrame?) {
        if (frame == null) return
        val w = frame.rotatedWidth
        val h = frame.rotatedHeight
        if (w > 0 && h > 0 && (w != lastW || h != lastH)) {
            lastW = w
            lastH = h
            val ratio = (w.toFloat() / h.toFloat()).coerceIn(0.2f, 5f)
            eglRenderer.setLayoutAspectRatio(ratio)
            post { onAspect?.invoke(ratio) }
        }
        eglRenderer.onFrame(frame)
    }

    override fun onSurfaceTextureAvailable(surface: SurfaceTexture, width: Int, height: Int) {
        if (initialized && !surfaceReady) {
            eglRenderer.createEglSurface(surface)
            surfaceReady = true
        }
    }

    override fun onSurfaceTextureSizeChanged(surface: SurfaceTexture, width: Int, height: Int) {}

    override fun onSurfaceTextureDestroyed(surface: SurfaceTexture): Boolean {
        if (initialized && surfaceReady) {
            surfaceReady = false
            val latch = CountDownLatch(1)
            try {
                eglRenderer.releaseEglSurface { latch.countDown() }
                latch.await(500, TimeUnit.MILLISECONDS)
            } catch (e: Exception) { }
        }
        return true
    }

    override fun onSurfaceTextureUpdated(surface: SurfaceTexture) {}
}

@Composable
fun WebRtcLiveView(
    modifier: Modifier = Modifier,
    isPaused: Boolean = false,
    onCaptureResult: (Bitmap, List<Offset>) -> Unit
) {
    val pausedState = rememberUpdatedState(isPaused)
    val captureState = rememberUpdatedState(onCaptureResult)
    val rendererHolder = remember { arrayOfNulls<DocTextureRenderer>(1) }
    var videoAspect by remember { mutableStateOf(0.75f) }
    var rendererEpoch by remember { mutableStateOf(0) }
    val sink = remember {
        object : VideoSink {
            override fun onFrame(frame: VideoFrame?) {
                if (!pausedState.value) rendererHolder[0]?.onFrame(frame)
            }
        }
    }
    val context = LocalContext.current

    DisposableEffect(Unit) {
        LiveFeedSession.start(context)
        val callback: (Bitmap, List<Offset>) -> Unit = { bmp, corners ->
            captureState.value.invoke(bmp, corners)
        }
        LiveFeedSession.captureCallback = callback
        LiveFeedSession.attach(sink)
        onDispose {
            LiveFeedSession.detach(sink)
            if (LiveFeedSession.captureCallback === callback) LiveFeedSession.captureCallback = null
            try { rendererHolder[0]?.releaseRenderer() } catch (e: Exception) {}
            rendererHolder[0] = null
        }
    }

    // Black-screen guard: video frames ARE arriving but the drawing surface is not ready -> rebuild the view.
    LaunchedEffect(Unit) {
        var badTicks = 0
        while (true) {
            delay(1200)
            val r = rendererHolder[0]
            if (LiveFeedSession.isReceivingFrames() && (r == null || !r.isSurfaceReady)) {
                badTicks++
                if (badTicks >= 2) {
                    badTicks = 0
                    try { r?.releaseRenderer() } catch (e: Exception) {}
                    rendererHolder[0] = null
                    rendererEpoch++
                }
            } else {
                badTicks = 0
            }
        }
    }

    // The zoom/pan layer (passed in `modifier`) wraps this whole box; the video is
    // centred and aspect-fitted inside it, exactly like the old SCALE_ASPECT_FIT.
    Box(modifier = modifier.fillMaxSize(), contentAlignment = Alignment.Center) {
        key(rendererEpoch) {
            AndroidView(
                modifier = Modifier.aspectRatio(videoAspect),
                factory = { ctx ->
                    LiveFeedSession.start(ctx)
                    DocTextureRenderer(ctx).apply {
                        onAspect = { a ->
                            // while a zoom region is active the frame is a crop: keep the box of the whole frame,
                            // otherwise the picture would shift by a few pixels every time the region changes
                            if (LiveFeedSession.requestedRoi == null && LiveFeedSession.activeRoi == null) {
                                videoAspect = a
                                LiveFeedSession.videoAspect = a
                            }
                        }
                        setup(LiveFeedSession.eglContext)
                        rendererHolder[0] = this
                    }
                }
            )
        }
    }
}

/** Full-screen "enter the host's pairing code" prompt. Cannot be dismissed until a code has been set. */
@Composable
private fun PairCodeDialog(
    canDismiss: Boolean,
    notice: String?,
    current: String,
    onSubmit: (String) -> Unit,
    onDismiss: () -> Unit
) {
    var text by remember { mutableStateOf("") }
    Dialog(
        onDismissRequest = { if (canDismiss) onDismiss() },
        properties = DialogProperties(
            dismissOnBackPress = canDismiss,
            dismissOnClickOutside = false,
            usePlatformDefaultWidth = false
        )
    ) {
        Surface(modifier = Modifier.fillMaxSize(), color = MaterialTheme.colorScheme.background) {
            Column(
                modifier = Modifier.fillMaxSize().padding(28.dp).statusBarsPadding(),
                horizontalAlignment = Alignment.CenterHorizontally,
                verticalArrangement = Arrangement.Center
            ) {
                Icon(Icons.Default.Lock, contentDescription = null, tint = MaterialTheme.colorScheme.primary, modifier = Modifier.size(44.dp))
                Spacer(Modifier.height(12.dp))
                Text("Pair with the host PC", fontSize = 22.sp, fontWeight = FontWeight.Bold, color = MaterialTheme.colorScheme.primary)
                Spacer(Modifier.height(8.dp))
                Text(
                    "Type the 8-character code (XXXX-XXXX) shown at the top of the DocSign Host program.",
                    textAlign = androidx.compose.ui.text.style.TextAlign.Center,
                    color = MaterialTheme.colorScheme.onSurfaceVariant
                )
                if (notice != null) {
                    Spacer(Modifier.height(10.dp))
                    Text(notice, color = Color(0xFFB45309), fontWeight = FontWeight.SemiBold,
                        textAlign = androidx.compose.ui.text.style.TextAlign.Center)
                }
                Spacer(Modifier.height(22.dp))
                OutlinedTextField(
                    value = text,
                    onValueChange = { v -> text = v.uppercase().filter { it.isLetterOrDigit() }.take(PAIR_CODE_LEN) },
                    singleLine = true,
                    placeholder = { Text("ABCD2345", letterSpacing = 3.sp, fontFamily = FontFamily.Monospace) },
                    textStyle = androidx.compose.ui.text.TextStyle(
                        fontSize = 26.sp, letterSpacing = 3.sp, fontFamily = FontFamily.Monospace,
                        fontWeight = FontWeight.Bold, textAlign = androidx.compose.ui.text.style.TextAlign.Center
                    ),
                    keyboardOptions = KeyboardOptions(capitalization = KeyboardCapitalization.Characters),
                    modifier = Modifier.width(300.dp)
                )
                Spacer(Modifier.height(18.dp))
                Button(
                    onClick = { onSubmit(text) },
                    enabled = text.length == PAIR_CODE_LEN,
                    shape = RoundedCornerShape(12.dp),
                    modifier = Modifier.width(300.dp).height(48.dp)
                ) { Text("Connect", fontSize = 16.sp, fontWeight = FontWeight.SemiBold) }
                if (canDismiss) {
                    TextButton(onClick = onDismiss) { Text("Cancel") }
                }
            }
        }
    }
}

/** A region of the full camera frame (top-left x/y and side length s, all 0..1) the host is sending at full detail. */
class ZoomRoi(val x: Float, val y: Float, val sx: Float, val sy: Float)

/** Where the aspect-fitted video sits inside a W x H box: [left, top, width, height]. */
private fun fitRect(w: Float, h: Float, aspect: Float): FloatArray {
    val a = aspect.coerceAtLeast(0.01f)
    val cw: Float
    val ch: Float
    if (w / h > a) { ch = h; cw = h * a } else { cw = w; ch = w / a }
    return floatArrayOf((w - cw) / 2f, (h - ch) / 2f, cw, ch)
}

@Composable
fun ZoomableLiveFeed(
    modifier: Modifier = Modifier,
    onCaptureResult: (Bitmap, List<Offset>) -> Unit,
    onStreamLive: (() -> Unit)? = null
) {
    val zoomState = remember { SmoothZoomState() }
    val zoomScope = rememberCoroutineScope()
    val isZoomedIn by remember { derivedStateOf { zoomState.scale > 1.05f } }
    val zoomLabel by remember { derivedStateOf { String.format("%.1f", zoomState.scale) } }
    val handshakeProgress = LiveFeedSession.progress
    val connectionStatus = LiveFeedSession.statusMessage
    var streamLiveTriggered by remember { mutableStateOf(false) }
    val activeRoi = LiveFeedSession.activeRoi
    val videoAspectNow = LiveFeedSession.videoAspect

    // Once the zoom settles, ask the host for just the visible part of the camera frame at full detail.
    LaunchedEffect(Unit) {
        snapshotFlow { Triple(zoomState.scale, zoomState.offset, LiveFeedSession.videoAspect) }
            .collectLatest { (sc, off, va) ->
                delay(450)
                val w = zoomState.viewSize.width.toFloat()
                val h = zoomState.viewSize.height.toFloat()
                if (w <= 0f || h <= 0f || LiveFeedSession.progress < 1f) return@collectLatest
                val cur = LiveFeedSession.requestedRoi
                if (sc < 1.15f) {
                    if (cur != null) LiveFeedSession.requestRoi(null)
                    return@collectLatest
                }
                val fr = fitRect(w, h, va)
                // visible area in whole-frame coordinates (0..1)
                val vx = ((-off.x / sc) - fr[0]) / fr[2]
                val vy = ((-off.y / sc) - fr[1]) / fr[3]
                val x1 = maxOf(vx, 0f)
                val y1 = maxOf(vy, 0f)
                val x2 = minOf(vx + (w / sc) / fr[2], 1f)
                val y2 = minOf(vy + (h / sc) / fr[3], 1f)
                val side = minOf(1f, maxOf(x2 - x1, y2 - y1) * 1.3f)      // 30% margin so small pans stay sharp
                if (side >= 0.9f) {
                    if (cur != null) LiveFeedSession.requestRoi(null)
                    return@collectLatest
                }
                if (cur != null) {
                    val covers = x1 >= cur.x - 0.01f && y1 >= cur.y - 0.01f &&
                            x2 <= cur.x + cur.sx + 0.01f && y2 <= cur.y + cur.sy + 0.01f
                    if (covers && cur.sx <= side * 1.5f) return@collectLatest
                }
                val rx = ((x1 + x2) / 2f - side / 2f).coerceIn(0f, 1f - side)
                val ry = ((y1 + y2) / 2f - side / 2f).coerceIn(0f, 1f - side)
                LiveFeedSession.requestRoi(ZoomRoi(rx, ry, side, side))
            }
    }

    LaunchedEffect(handshakeProgress) {
        if (handshakeProgress >= 1.0f && !streamLiveTriggered) {
            streamLiveTriggered = true
            onStreamLive?.invoke()
        }
    }
    var streamPaused by remember { mutableStateOf(false) }
    val streamQuality = LiveFeedSession.streamQuality
    val qualityLevels = LiveFeedSession.qualityLevels
    val uiContext = LocalContext.current

    fun sendToHost(json: JSONObject) {
        val ws = signalingWebSocket
        if (ws != null && isSignalingConnected) ws.send(json.toString())
    }

    Box(
        modifier = modifier
            .shadow(6.dp, RoundedCornerShape(14.dp))
            .clip(RoundedCornerShape(14.dp))
            .background(Color(0xFF0F172A))
            .onSizeChanged { zoomState.viewSize = it }
            .smoothZoomGestures(zoomState, zoomScope)
    ) {
        WebRtcLiveView(
            modifier = Modifier
                .fillMaxSize()
                .graphicsLayer {
                    val sc = zoomState.scale
                    var scx = sc
                    var scy = sc
                    var ox = zoomState.offset.x
                    var oy = zoomState.offset.y
                    val roi = activeRoi
                    val vw = zoomState.viewSize.width.toFloat()
                    val vh = zoomState.viewSize.height.toFloat()
                    if (roi != null && vw > 0f && vh > 0f) {
                        // The frames already show only the region `roi`, so map them onto the same screen spot
                        // the whole-frame view would have had - the picture just becomes sharper.
                        val fr = fitRect(vw, vh, videoAspectNow)
                        ox += sc * (fr[0] * (1f - roi.sx) + roi.x * fr[2])
                        oy += sc * (fr[1] * (1f - roi.sy) + roi.y * fr[3])
                        scx = sc * roi.sx
                        scy = sc * roi.sy
                    }
                    scaleX = scx
                    scaleY = scy
                    translationX = ox
                    translationY = oy
                    transformOrigin = TransformOrigin(0f, 0f)
                },
            isPaused = streamPaused,
            onCaptureResult = onCaptureResult
        )

        if (handshakeProgress >= 1.0f) {
            Row(
                modifier = Modifier
                    .align(Alignment.BottomStart)
                    .padding(8.dp)
                    .shadow(4.dp, RoundedCornerShape(50))
                    .clip(RoundedCornerShape(50))
                    .background(Color.Black.copy(alpha = 0.55f))
                    .padding(horizontal = 6.dp, vertical = 2.dp),
                verticalAlignment = Alignment.CenterVertically
            ) {
                TextButton(
                    contentPadding = PaddingValues(horizontal = 8.dp, vertical = 2.dp),
                    onClick = {
                        streamPaused = !streamPaused
                        sendToHost(JSONObject().put("type", "stream_control").put("paused", streamPaused))
                    }
                ) {
                    Text(if (streamPaused) "▶ Resume" else "⏸ Pause", color = Color.White, fontSize = 12.sp)
                }
                Text("·", color = Color.White.copy(alpha = 0.5f))
                TextButton(
                    contentPadding = PaddingValues(horizontal = 8.dp, vertical = 2.dp),
                    onClick = {
                        val next = qualityLevels[(qualityLevels.indexOf(streamQuality) + 1) % qualityLevels.size]
                        LiveFeedSession.updateStreamQuality(next)
                        if (next.startsWith("High")) {
                            android.widget.Toast.makeText(
                                uiContext,
                                "High quality uses a lot of mobile data. Use it only on Wi-Fi or for short checks.",
                                android.widget.Toast.LENGTH_LONG
                            ).show()
                        }
                    }
                ) {
                    Text(
                        if (streamQuality.startsWith("High")) "$streamQuality ⚠" else streamQuality,
                        color = if (streamQuality.startsWith("High")) Color(0xFFFFB74D) else Color.White,
                        fontSize = 12.sp
                    )
                }
                if (isZoomedIn) {
                    Text("·", color = Color.White.copy(alpha = 0.5f))
                    TextButton(
                        contentPadding = PaddingValues(horizontal = 8.dp, vertical = 2.dp),
                        onClick = { zoomState.animateReset(zoomScope) }
                    ) {
                        Text("${zoomLabel}x (Reset)", color = Color(0xFF93C5FD), fontSize = 12.sp)
                    }
                }
            }
        }

        if (handshakeProgress >= 1.0f && !hostMachineConnected) {
            Text(
                "Machine offline · live view only",
                color = Color.White,
                fontSize = 11.sp,
                fontWeight = FontWeight.SemiBold,
                modifier = Modifier
                    .align(Alignment.TopEnd)
                    .padding(8.dp)
                    .clip(RoundedCornerShape(50))
                    .background(Color(0xCCB45309))
                    .padding(horizontal = 10.dp, vertical = 3.dp)
            )
        }

        AnimatedVisibility(
            visible = handshakeProgress < 1.0f,
            enter = fadeIn(),
            exit = fadeOut()
        ) {
            Box(
                modifier = Modifier
                    .fillMaxSize()
                    .background(Color.Black.copy(alpha = 0.85f)),
                contentAlignment = Alignment.Center
            ) {
                Column(horizontalAlignment = Alignment.CenterHorizontally) {
                    CircularProgressIndicator(
                        progress = handshakeProgress.coerceAtLeast(0.05f),
                        color = MaterialTheme.colorScheme.secondary,
                        modifier = Modifier.size(52.dp),
                        strokeWidth = 4.dp
                    )
                    Spacer(Modifier.height(18.dp))
                    Text(
                        text = connectionStatus,
                        color = Color.White,
                        style = MaterialTheme.typography.titleMedium,
                        fontWeight = FontWeight.Medium
                    )
                }
            }
        }
    }
}

private fun signatureDir(context: Context): File =
    File(context.filesDir, "signatures").apply { mkdirs() }

private fun sanitizeTemplateFileName(name: String): String =
    name.trim().ifBlank { "Signature" }
        .replace(Regex("[^A-Za-z0-9 _-]"), "_")
        .take(60)

data class SignatureTemplateInfo(val displayName: String, val file: File)

private fun listSignatureTemplates(context: Context): List<SignatureTemplateInfo> {
    val dir = signatureDir(context)
    val files = dir.listFiles { f -> f.isFile && f.extension == "sig" } ?: emptyArray()
    return files.mapNotNull { f ->
        try {
            val firstLine = f.bufferedReader().use { it.readLine() } ?: return@mapNotNull null
            SignatureTemplateInfo(firstLine, f)
        } catch (e: Exception) {
            null
        }
    }.sortedBy { it.displayName.lowercase() }
}

private fun hasSavedSignature(context: Context): Boolean =
    listSignatureTemplates(context).isNotEmpty()

private fun saveSignatureTemplate(
    context: Context,
    name: String,
    strokes: List<List<Offset>>,
    widths: List<Float>,
    canvasSize: IntSize
) {
    val displayName = name.trim().ifBlank { "Signature" }
    val fileNameBase = sanitizeTemplateFileName(displayName)
    val existing = listSignatureTemplates(context).firstOrNull { it.displayName.equals(displayName, ignoreCase = true) }
    var target = existing?.file ?: File(signatureDir(context), "$fileNameBase.sig")
    if (existing == null) {
        var suffix = 2
        while (target.exists()) {
            target = File(signatureDir(context), "${fileNameBase}_${suffix}.sig")
            suffix++
        }
    }

    val sb = StringBuilder()
    sb.append(displayName).append('\n')
    sb.append(canvasSize.width).append(' ').append(canvasSize.height).append('\n')
    sb.append(widths.joinToString(" ")).append('\n')
    strokes.forEach { stroke ->
        sb.append(stroke.joinToString(" ") { "${it.x},${it.y}" }).append('\n')
    }
    target.writeText(sb.toString())
}

private fun renameSignatureTemplate(context: Context, file: File, newName: String): Boolean {
    if (!file.exists()) return false
    return try {
        val lines = file.readLines().toMutableList()
        if (lines.isEmpty()) return false
        val cleanName = newName.trim().ifBlank { "Signature" }
        lines[0] = cleanName
        file.writeText(lines.joinToString("\n") + "\n")
        true
    } catch (e: Exception) {
        false
    }
}

private fun loadSignatureTemplate(file: File): Triple<List<List<Offset>>, List<Float>, IntSize>? {
    if (!file.exists()) return null
    return try {
        val lines = file.readLines()
        if (lines.size < 3) return null
        val (w, h) = lines[1].split(" ").map { it.toInt() }
        val widths = lines[2].split(" ").filter { it.isNotBlank() }.map { it.toFloat() }
        val strokes = lines.drop(3).filter { it.isNotBlank() }.map { line ->
            line.trim().split(" ").map { pt ->
                val (x, y) = pt.split(",")
                Offset(x.toFloat(), y.toFloat())
            }
        }
        Triple(strokes, widths, IntSize(w, h))
    } catch (e: Exception) {
        null
    }
}

private fun deleteSignatureTemplate(file: File) {
    try { file.delete() } catch (e: Exception) { }
}

private fun buildPathFromPoints(points: List<Offset>): Path {
    val path = Path()
    if (points.isNotEmpty()) {
        path.moveTo(points[0].x, points[0].y)
        for (i in 1 until points.size) {
            val prev = points[i - 1]
            val cur = points[i]
            path.quadraticBezierTo(prev.x, prev.y, (prev.x + cur.x) / 2f, (prev.y + cur.y) / 2f)
        }
        path.lineTo(points.last().x, points.last().y)
    }
    return path
}

private fun sanitizePdfName(raw: String): String =
    raw.trim()
        .replace(Regex("(?i)\\.pdf$"), "")
        .replace(Regex("[\\\\/:*?\"<>|]"), "_")
        .trim()
        .take(80)
        .ifBlank { "DocSign" }

private fun defaultPdfName(prefix: String): String =
    prefix + "_" + java.text.SimpleDateFormat("yyyyMMdd_HHmm", java.util.Locale.getDefault()).format(java.util.Date())

/** Asks for a file name, then lets the user choose: Download (save to Downloads) or Share. */
@Composable
private fun PdfNameDialog(
    defaultName: String,
    onDismiss: () -> Unit,
    onDownload: (String) -> Unit,
    onShare: (String) -> Unit
) {
    var name by remember { mutableStateOf(defaultName) }
    AlertDialog(
        onDismissRequest = onDismiss,
        title = { Text("Name your PDF") },
        text = {
            Column(verticalArrangement = Arrangement.spacedBy(8.dp)) {
                OutlinedTextField(
                    value = name,
                    onValueChange = { name = it },
                    singleLine = true,
                    label = { Text("File name (.pdf is added)") },
                    modifier = Modifier.fillMaxWidth()
                )
                Text(
                    "Then choose: Download saves it to your Downloads folder, Share opens the share sheet.",
                    fontSize = 12.sp,
                    color = MaterialTheme.colorScheme.onSurfaceVariant
                )
            }
        },
        confirmButton = {
            Row(horizontalArrangement = Arrangement.spacedBy(4.dp)) {
                OutlinedButton(onClick = { val n = sanitizePdfName(name); onDismiss(); onShare(n) }) { Text("Share") }
                Button(onClick = { val n = sanitizePdfName(name); onDismiss(); onDownload(n) }) { Text("Download") }
            }
        },
        dismissButton = { TextButton(onClick = onDismiss) { Text("Cancel") } }
    )
}

@Composable
fun CropScreen(
    rawBitmap: Bitmap?,
    initialCorners: List<Offset>?,
    statusMessage: String?,
    onRetake: () -> Unit,
    onConfirm: (List<Offset>) -> Unit,
    onExportPdf: (List<Offset>, String, Boolean) -> Unit = { _, _, _ -> }
) {
    var boxSize by remember { mutableStateOf(IntSize.Zero) }
    val corners = remember(rawBitmap) {
        mutableStateListOf<Offset>().apply {
            if (initialCorners != null && initialCorners.size == 4) {
                addAll(initialCorners)
            } else if (rawBitmap != null) {
                val w = rawBitmap.width.toFloat()
                val h = rawBitmap.height.toFloat()
                val mx = w * 0.08f
                val my = h * 0.08f
                addAll(listOf(Offset(mx, my), Offset(w - mx, my), Offset(w - mx, h - my), Offset(mx, h - my)))
            }
        }
    }
    var activeDragIndex by remember { mutableStateOf<Int?>(null) }
    val cropState = remember { SmoothZoomState() }
    val cropScope = rememberCoroutineScope()
    val cropZoomedIn by remember { derivedStateOf { cropState.scale > 1.05f } }
    var showPdfDialog by remember { mutableStateOf(false) }
    if (showPdfDialog) {
        PdfNameDialog(
            defaultName = defaultPdfName("DocSign_Scan"),
            onDismiss = { showPdfDialog = false },
            onDownload = { n -> onExportPdf(corners.toList(), n, false) },
            onShare = { n -> onExportPdf(corners.toList(), n, true) }
        )
    }

    Column(Modifier.fillMaxSize().padding(horizontal = 6.dp, vertical = 3.dp)) {
        Box(
            modifier = Modifier
                .weight(1f)
                .fillMaxWidth()
                .shadow(6.dp, RoundedCornerShape(14.dp))
                .clip(RoundedCornerShape(14.dp))
                .background(Color(0xFF0F172A))
                .onSizeChanged { boxSize = it; cropState.viewSize = it }
                .smoothZoomGestures(cropState, cropScope) { activeDragIndex == null },
            contentAlignment = Alignment.Center
        ) {
            if (rawBitmap != null && corners.size == 4 && boxSize != IntSize.Zero) {
                val imgAspect = rawBitmap.width.toFloat() / rawBitmap.height.toFloat()
                val boxAspect = boxSize.width.toFloat() / boxSize.height.toFloat()
                val fittedWidth: Int
                val fittedHeight: Int
                if (imgAspect > boxAspect) {
                    fittedWidth = boxSize.width
                    fittedHeight = (boxSize.width / imgAspect).roundToInt()
                } else {
                    fittedHeight = boxSize.height
                    fittedWidth = (boxSize.height * imgAspect).roundToInt()
                }

                val scaleX = fittedWidth.toFloat() / rawBitmap.width.toFloat()
                val scaleY = fittedHeight.toFloat() / rawBitmap.height.toFloat()

                Box(
                    Modifier
                        .fillMaxSize()
                        .graphicsLayer {
                            this.scaleX = cropState.scale
                            this.scaleY = cropState.scale
                            translationX = cropState.offset.x
                            translationY = cropState.offset.y
                            transformOrigin = TransformOrigin(0f, 0f)
                        },
                    contentAlignment = Alignment.Center
                ) {
                    Box(
                        modifier = Modifier.size(
                            width = (fittedWidth / LocalContext.current.resources.displayMetrics.density).dp,
                            height = (fittedHeight / LocalContext.current.resources.displayMetrics.density).dp
                        )
                    ) {
                        Image(
                            bitmap = remember(rawBitmap) { rawBitmap.asImageBitmap() },
                            contentDescription = "Captured document",
                            contentScale = ContentScale.FillBounds,
                            modifier = Modifier.fillMaxSize()
                        )

                        Canvas(modifier = Modifier.fillMaxSize()) {
                            val displayPoints = corners.map { Offset(it.x * scaleX, it.y * scaleY) }
                            val path = Path().apply {
                                moveTo(displayPoints[0].x, displayPoints[0].y)
                                displayPoints.drop(1).forEach { lineTo(it.x, it.y) }
                                close()
                            }
                            val invZoom = (1f / cropState.scale).coerceIn(0.25f, 1f)
                            drawPath(path, color = Color(0xFF3B82F6), style = Stroke(width = 5f * invZoom))

                            displayPoints.forEachIndexed { idx, p ->
                                val isDragging = activeDragIndex == idx
                                drawCircle(
                                    color = Color.White,
                                    radius = (if (isDragging) 30f else 24f) * invZoom,
                                    center = p
                                )
                                drawCircle(
                                    color = Color(0xFF3B82F6),
                                    radius = (if (isDragging) 21f else 16f) * invZoom,
                                    center = p
                                )
                            }
                        }

                        corners.forEachIndexed { index, corner ->
                            val displayX = corner.x * scaleX
                            val displayY = corner.y * scaleY
                            Box(
                                modifier = Modifier
                                    .offset { IntOffset((displayX - 38).roundToInt(), (displayY - 38).roundToInt()) }
                                    .size(76.dp)
                                    .pointerInput(index, scaleX, scaleY) {
                                        detectDragGestures(
                                            onDragStart = { activeDragIndex = index },
                                            onDragEnd = { activeDragIndex = null },
                                            onDragCancel = { activeDragIndex = null }
                                        ) { change, dragAmount ->
                                            change.consume()
                                            activeDragIndex = index
                                            val dxRaw = dragAmount.x / scaleX
                                            val dyRaw = dragAmount.y / scaleY
                                            val updated = corners[index] + Offset(dxRaw, dyRaw)
                                            corners[index] = Offset(
                                                updated.x.coerceIn(0f, rawBitmap.width.toFloat()),
                                                updated.y.coerceIn(0f, rawBitmap.height.toFloat())
                                            )
                                        }
                                    }
                            )
                        }
                    }
                }

                val draggedIdx = activeDragIndex
                if (draggedIdx != null) {
                    val activeCorner = corners[draggedIdx]
                    val activeDisplayX = activeCorner.x * scaleX
                    val activeDisplayY = activeCorner.y * scaleY
                    val placeOnRight = activeDisplayX < fittedWidth * 0.45f && activeDisplayY < fittedHeight * 0.45f

                    Box(
                        modifier = Modifier
                            .align(if (placeOnRight) Alignment.TopEnd else Alignment.TopStart)
                            .padding(12.dp)
                            .size(118.dp)
                            .shadow(10.dp, CircleShape)
                            .clip(CircleShape)
                            .background(Color.Black)
                            .border(3.dp, Color(0xFF3B82F6), CircleShape)
                    ) {
                        Canvas(modifier = Modifier.fillMaxSize()) {
                            val zoomFactor = 3.2f
                            val magScaleX = scaleX * zoomFactor
                            val magScaleY = scaleY * zoomFactor

                            drawIntoCanvas { canvas ->
                                val matrix = android.graphics.Matrix().apply {
                                    postTranslate(-activeCorner.x, -activeCorner.y)
                                    postScale(magScaleX, magScaleY)
                                    postTranslate(size.width / 2f, size.height / 2f)
                                }
                                val paint = Paint(Paint.ANTI_ALIAS_FLAG or Paint.FILTER_BITMAP_FLAG)
                                canvas.nativeCanvas.drawBitmap(rawBitmap, matrix, paint)
                            }

                            val center = Offset(size.width / 2f, size.height / 2f)
                            drawLine(
                                color = Color(0xFF3B82F6),
                                start = Offset(0f, center.y),
                                end = Offset(size.width, center.y),
                                strokeWidth = 3f
                            )
                            drawLine(
                                color = Color(0xFF3B82F6),
                                start = Offset(center.x, 0f),
                                end = Offset(center.x, size.height),
                                strokeWidth = 3f
                            )
                            drawCircle(color = Color.White, radius = 4.5f, center = center)
                        }
                    }
                }
            } else {
                Box(Modifier.fillMaxSize(), contentAlignment = Alignment.Center) {
                    Text("No capture available. Please go back.", color = Color.Gray)
                }
            }

            if (activeDragIndex == null) {
                Row(
                    modifier = Modifier
                        .align(Alignment.TopStart)
                        .padding(8.dp)
                        .clip(RoundedCornerShape(50))
                        .background(Color.Black.copy(alpha = 0.55f))
                        .padding(horizontal = 4.dp),
                    verticalAlignment = Alignment.CenterVertically
                ) {
                    Text(
                        "Adjust corners",
                        color = Color.White,
                        fontSize = 11.sp,
                        fontWeight = FontWeight.SemiBold,
                        modifier = Modifier.padding(horizontal = 8.dp)
                    )
                    if (rawBitmap != null && initialCorners != null && initialCorners.size == 4) {
                        TextButton(
                            contentPadding = PaddingValues(horizontal = 8.dp, vertical = 0.dp),
                            modifier = Modifier.height(28.dp),
                            onClick = {
                                corners.clear()
                                corners.addAll(initialCorners)
                            }
                        ) { Text("Auto-Edges", fontSize = 11.sp, color = Color(0xFF93C5FD)) }
                    }
                    if (cropZoomedIn) {
                        TextButton(
                            contentPadding = PaddingValues(horizontal = 8.dp, vertical = 0.dp),
                            modifier = Modifier.height(28.dp),
                            onClick = { cropState.animateReset(cropScope) }
                        ) { Text("Reset zoom", fontSize = 11.sp, color = Color(0xFF93C5FD)) }
                    }
                }
            }
        }

        Spacer(Modifier.height(4.dp))

        Row(
            Modifier.fillMaxWidth(),
            horizontalArrangement = Arrangement.spacedBy(10.dp)
        ) {
            OutlinedButton(
                onClick = onRetake,
                modifier = Modifier.weight(0.85f).height(46.dp),
                shape = RoundedCornerShape(12.dp),
                contentPadding = PaddingValues(horizontal = 6.dp)
            ) { Text("Retake", fontSize = 14.sp, maxLines = 1, softWrap = false) }

            // DOWNLOAD #1 — cropped scan as PDF.
            OutlinedButton(
                enabled = corners.size == 4 && rawBitmap != null,
                onClick = { showPdfDialog = true },
                modifier = Modifier.weight(0.55f).height(46.dp),
                shape = RoundedCornerShape(12.dp),
                contentPadding = PaddingValues(horizontal = 4.dp)
            ) {
                Icon(Icons.Default.PictureAsPdf, contentDescription = "Download cropped PDF", tint = MaterialTheme.colorScheme.secondary, modifier = Modifier.size(22.dp))
            }

            Button(
                enabled = corners.size == 4,
                onClick = { onConfirm(corners.toList()) },
                modifier = Modifier.weight(1.3f).height(46.dp),
                shape = RoundedCornerShape(12.dp),
                contentPadding = PaddingValues(horizontal = 6.dp)
            ) { Text("Confirm Scan", fontSize = 14.sp, fontWeight = FontWeight.SemiBold, maxLines = 1, softWrap = false) }
        }

        if (statusMessage != null) {
            Text(
                statusMessage,
                modifier = Modifier.fillMaxWidth().padding(top = 4.dp),
                style = MaterialTheme.typography.bodySmall,
                color = MaterialTheme.colorScheme.primary
            )
        }
    }
}

@Composable
fun LiveFeedScreen(
    statusMessage: String?,
    streamEnabled: Boolean = true,
    showAsk: Boolean = false,
    onStartStream: () -> Unit = {},
    onDismissAsk: () -> Unit = {},
    onCapture: () -> Unit,
    onCaptureResult: (Bitmap, List<Offset>) -> Unit
) {
    Column(Modifier.fillMaxSize().padding(horizontal = 6.dp, vertical = 3.dp)) {
        Box(modifier = Modifier.weight(1f).fillMaxWidth()) {
            if (streamEnabled) {
                ZoomableLiveFeed(
                    modifier = Modifier.fillMaxSize(),
                    onCaptureResult = onCaptureResult
                )
                Surface(
                    color = Color(0xFFE8F5EE).copy(alpha = 0.92f),
                    shape = RoundedCornerShape(50),
                    modifier = Modifier.align(Alignment.TopStart).padding(8.dp)
                ) {
                    Text(
                        "A4 LIVE · AUTO-CROP ACTIVE",
                        modifier = Modifier.padding(horizontal = 8.dp, vertical = 2.dp),
                        color = Color(0xFF067647),
                        style = MaterialTheme.typography.labelSmall,
                        fontWeight = FontWeight.Bold
                    )
                }
            } else {
                Column(
                    Modifier
                        .fillMaxSize()
                        .clip(RoundedCornerShape(14.dp))
                        .background(Color(0xFF0F172A)),
                    horizontalAlignment = Alignment.CenterHorizontally,
                    verticalArrangement = Arrangement.Center
                ) {
                    Text("Live feed is off", color = Color.White, fontSize = 16.sp, fontWeight = FontWeight.SemiBold)
                    Spacer(Modifier.height(12.dp))
                    Button(onClick = onStartStream, shape = RoundedCornerShape(12.dp)) {
                        Text("Start live stream")
                    }
                }
            }
        }

        Button(
            onClick = onCapture,
            enabled = streamEnabled,
            modifier = Modifier.fillMaxWidth().padding(top = 4.dp).height(44.dp),
            shape = RoundedCornerShape(12.dp)
        ) {
            Text("Capture Document", fontSize = 16.sp, fontWeight = FontWeight.SemiBold)
        }

        if (statusMessage != null) {
            Text(
                statusMessage,
                modifier = Modifier.fillMaxWidth().padding(top = 4.dp),
                style = MaterialTheme.typography.bodySmall,
                color = MaterialTheme.colorScheme.primary
            )
        }
    }

    if (showAsk) {
        AlertDialog(
            onDismissRequest = onDismissAsk,
            title = { Text("Start live stream?") },
            text = { Text("The camera feed uses data. Start it now for the new document, or keep it off until you need it.") },
            confirmButton = { Button(onClick = onStartStream) { Text("Start stream") } },
            dismissButton = { TextButton(onClick = onDismissAsk) { Text("Not now") } }
        )
    }
}

@Composable
fun WatchSigningScreen(
    statusMessage: String?,
    signedPreviewBitmap: Bitmap?,
    controlsBusy: Boolean = false,
    scanBusy: Boolean = false,
    onScanSignedPdf: (String, Boolean) -> Unit = { _, _ -> },
    onPauseRequested: () -> Unit,
    onSignAgain: () -> Unit,
    onNewDocument: () -> Unit,
    onCaptureResult: (Bitmap, List<Offset>) -> Unit,
    onStreamLive: () -> Unit
) {
    var showDoodlePreview by remember { mutableStateOf(false) }
    val context = LocalContext.current
    var downloadStatus by remember { mutableStateOf<String?>(null) }
    var showPdfDialog by remember { mutableStateOf(false) }
    if (showPdfDialog) {
        PdfNameDialog(
            defaultName = defaultPdfName("DocSign_Signed"),
            onDismiss = { showPdfDialog = false },
            onDownload = { n -> onScanSignedPdf(n, false) },
            onShare = { n -> onScanSignedPdf(n, true) }
        )
    }

    Column(Modifier.fillMaxSize().padding(horizontal = 6.dp, vertical = 3.dp)) {
        Box(modifier = Modifier.weight(1f).fillMaxWidth()) {
            ZoomableLiveFeed(
                modifier = Modifier.fillMaxSize(),
                onCaptureResult = onCaptureResult,
                onStreamLive = onStreamLive
            )
            Surface(
                color = Color.Black.copy(alpha = 0.55f),
                shape = RoundedCornerShape(50),
                modifier = Modifier.align(Alignment.TopStart).padding(8.dp)
            ) {
                Text(
                    "LIVE EXECUTION",
                    modifier = Modifier.padding(horizontal = 10.dp, vertical = 3.dp),
                    color = Color.White,
                    style = MaterialTheme.typography.labelSmall,
                    fontWeight = FontWeight.Bold
                )
            }

            if (signedPreviewBitmap != null) {
                Row(
                    modifier = Modifier
                        .align(Alignment.TopEnd)
                        .padding(12.dp),
                    horizontalArrangement = Arrangement.spacedBy(8.dp)
                ) {
                    Box(
                        modifier = Modifier
                            .size(42.dp)
                            .shadow(6.dp, CircleShape)
                            .clip(CircleShape)
                            .background(MaterialTheme.colorScheme.secondary.copy(alpha = if (scanBusy) 0.4f else 0.9f))
                            .border(1.5.dp, Color.White.copy(alpha = 0.8f), CircleShape)
                            .clickable(enabled = !scanBusy) {
                                // Scan the real signed paper with the host camera and save it as a PDF,
                                // using the crop corners already confirmed for this document.
                                downloadStatus = null
                                showPdfDialog = true
                            },
                        contentAlignment = Alignment.Center
                    ) {
                        Icon(
                            imageVector = Icons.Default.PictureAsPdf,
                            contentDescription = "Download Signed PDF",
                            tint = Color.White,
                            modifier = Modifier.size(20.dp)
                        )
                    }

                    Box(
                        modifier = Modifier
                            .size(42.dp)
                            .shadow(6.dp, CircleShape)
                            .clip(CircleShape)
                            .background(MaterialTheme.colorScheme.secondary.copy(alpha = if (scanBusy) 0.4f else 0.9f))
                            .border(1.5.dp, Color.White.copy(alpha = 0.8f), CircleShape)
                            .clickable(enabled = !scanBusy) {
                                downloadStatus = null
                                showPdfDialog = true
                            },
                        contentAlignment = Alignment.Center
                    ) {
                        Icon(
                            imageVector = Icons.Default.Share,
                            contentDescription = "Share Signed PDF",
                            tint = Color.White,
                            modifier = Modifier.size(20.dp)
                        )
                    }

                    Box(
                        modifier = Modifier
                            .size(42.dp)
                            .shadow(6.dp, CircleShape)
                            .clip(CircleShape)
                            .background(MaterialTheme.colorScheme.primary.copy(alpha = 0.9f))
                            .border(1.5.dp, Color.White.copy(alpha = 0.8f), CircleShape)
                            .clickable { showDoodlePreview = true },
                        contentAlignment = Alignment.Center
                    ) {
                        Canvas(modifier = Modifier.size(20.dp)) {
                            val w = size.width
                            val h = size.height
                            val eyePath = Path().apply {
                                moveTo(0f, h / 2f)
                                quadraticBezierTo(w / 2f, 0f, w, h / 2f)
                                quadraticBezierTo(w / 2f, h, 0f, h / 2f)
                                close()
                            }
                            drawPath(eyePath, color = Color.White, style = Stroke(width = 3.5f))
                            drawCircle(color = Color.White, radius = w * 0.18f, center = Offset(w / 2f, h / 2f))
                        }
                    }
                }
            }
        }

        Spacer(Modifier.height(6.dp))

        Button(
            onClick = onPauseRequested,
            enabled = !controlsBusy,
            modifier = Modifier.fillMaxWidth().height(46.dp),
            shape = RoundedCornerShape(12.dp)
        ) { Text(if (controlsBusy) "Working..." else "Pause machine", fontSize = 15.sp, fontWeight = FontWeight.Bold) }

        Spacer(Modifier.height(6.dp))

        Row(
            Modifier.fillMaxWidth(),
            horizontalArrangement = Arrangement.spacedBy(10.dp)
        ) {
            OutlinedButton(
                onClick = onSignAgain,
                enabled = !scanBusy,
                modifier = Modifier.weight(1f).height(46.dp),
                shape = RoundedCornerShape(12.dp)
            ) { Text("Sign Again") }

            OutlinedButton(
                onClick = onNewDocument,
                modifier = Modifier.weight(1f).height(46.dp),
                shape = RoundedCornerShape(12.dp)
            ) { Text("New Document") }
        }

        val msg = downloadStatus ?: statusMessage
        if (msg != null) {
            Text(
                msg,
                modifier = Modifier.fillMaxWidth().padding(top = 4.dp),
                style = MaterialTheme.typography.bodySmall,
                color = MaterialTheme.colorScheme.primary
            )
        }
    }

    if (showDoodlePreview && signedPreviewBitmap != null) {
        Dialog(onDismissRequest = { showDoodlePreview = false }) {
            val previewState = remember { SmoothZoomState() }
            val previewScope = rememberCoroutineScope()

            Box(
                modifier = Modifier
                    .fillMaxWidth()
                    .fillMaxHeight(0.85f)
                    .shadow(12.dp, RoundedCornerShape(16.dp))
                    .clip(RoundedCornerShape(16.dp))
                    .background(MaterialTheme.colorScheme.surface)
                    .padding(12.dp)
            ) {
                Column(Modifier.fillMaxSize()) {
                    Row(
                        modifier = Modifier.fillMaxWidth(),
                        horizontalArrangement = Arrangement.SpaceBetween,
                        verticalAlignment = Alignment.CenterVertically
                    ) {
                        Text(
                            "Doodled Signature Preview",
                            style = MaterialTheme.typography.titleMedium,
                            fontWeight = FontWeight.Bold,
                            color = MaterialTheme.colorScheme.onSurface
                        )
                        TextButton(onClick = { showDoodlePreview = false }) {
                            Text("Close", fontWeight = FontWeight.Bold)
                        }
                    }

                    Spacer(Modifier.height(6.dp))

                    Box(
                        modifier = Modifier
                            .weight(1f)
                            .fillMaxWidth()
                            .clip(RoundedCornerShape(12.dp))
                            .background(Color.Black.copy(alpha = 0.05f))
                            .onSizeChanged { previewState.viewSize = it }
                            .smoothZoomGestures(previewState, previewScope),
                        contentAlignment = Alignment.Center
                    ) {
                        Image(
                            bitmap = signedPreviewBitmap.asImageBitmap(),
                            contentDescription = "Signed document preview",
                            contentScale = ContentScale.Fit,
                            modifier = Modifier
                                .fillMaxSize()
                                .graphicsLayer {
                                    scaleX = previewState.scale
                                    scaleY = previewState.scale
                                    translationX = previewState.offset.x
                                    translationY = previewState.offset.y
                                    transformOrigin = TransformOrigin(0f, 0f)
                                }
                        )
                    }
                }
            }
        }
    }
}

@Composable
fun PauseConfirmScreen(
    statusMessage: String?,
    controlsBusy: Boolean = false,
    onContinue: () -> Unit,
    onAbort: () -> Unit,
    onCaptureResult: (Bitmap, List<Offset>) -> Unit
) {
    Column(Modifier.fillMaxSize().padding(horizontal = 6.dp, vertical = 3.dp)) {
        Box(modifier = Modifier.weight(1f).fillMaxWidth()) {
            ZoomableLiveFeed(modifier = Modifier.fillMaxSize(), onCaptureResult = onCaptureResult)
            Surface(
                color = MaterialTheme.colorScheme.error.copy(alpha = 0.9f),
                shape = RoundedCornerShape(50),
                modifier = Modifier.align(Alignment.TopStart).padding(8.dp)
            ) {
                Text(
                    "MACHINE PAUSED IN PLACE",
                    modifier = Modifier.padding(horizontal = 10.dp, vertical = 3.dp),
                    color = Color.White,
                    style = MaterialTheme.typography.labelSmall,
                    fontWeight = FontWeight.Bold
                )
            }
        }

        Spacer(Modifier.height(6.dp))

        Row(
            Modifier.fillMaxWidth(),
            horizontalArrangement = Arrangement.spacedBy(12.dp)
        ) {
            Button(
                onClick = onContinue,
                enabled = !controlsBusy,
                colors = ButtonDefaults.buttonColors(containerColor = Color(0xFF10B981)),
                modifier = Modifier.weight(1f).height(48.dp),
                shape = RoundedCornerShape(12.dp)
            ) { Text("Resume") }

            Button(
                onClick = onAbort,
                enabled = !controlsBusy,
                colors = ButtonDefaults.buttonColors(containerColor = MaterialTheme.colorScheme.error),
                modifier = Modifier.weight(1f).height(48.dp),
                shape = RoundedCornerShape(12.dp)
            ) { Text("Stop job") }
        }

        Text(
            "Resuming continues from the exact paused location with the pen held in place. Stopping cancels queued motion and returns the toolhead to origin.",
            modifier = Modifier.fillMaxWidth().padding(top = 6.dp),
            style = MaterialTheme.typography.bodySmall,
            color = MaterialTheme.colorScheme.onSurfaceVariant
        )

        if (statusMessage != null) {
            Text(
                statusMessage,
                modifier = Modifier.fillMaxWidth().padding(top = 6.dp),
                style = MaterialTheme.typography.bodySmall,
                color = MaterialTheme.colorScheme.primary
            )
        }
    }
}

private class FloatingSignatureState(
    val baseStrokes: List<List<Offset>>,
    val baseWidths: List<Float>,
    val baseWidth: Float,
    val baseHeight: Float,
    initialCenter: Offset,
    initialScale: Float = 1f
) {
    var center by mutableStateOf(initialCenter)
    var scale by mutableStateOf(initialScale)

    private val padding: Float = 10f

    val boxW: Float get() = (baseWidth * scale) + padding * 2f
    val boxH: Float get() = (baseHeight * scale) + padding * 2f

    fun cornerPos(i: Int): Offset {
        val hx = boxW / 2f
        val hy = boxH / 2f
        return when (i) {
            0 -> Offset(center.x - hx, center.y - hy)
            1 -> Offset(center.x + hx, center.y - hy)
            2 -> Offset(center.x - hx, center.y + hy)
            else -> Offset(center.x + hx, center.y + hy)
        }
    }

    fun contains(p: Offset, margin: Float): Boolean =
        abs(p.x - center.x) <= boxW / 2f + margin && abs(p.y - center.y) <= boxH / 2f + margin

    fun transformedStrokes(): List<MutableList<Offset>> {
        return baseStrokes.map { stroke ->
            stroke.map { pt ->
                Offset(center.x + pt.x * scale, center.y + pt.y * scale)
            }.toMutableList()
        }
    }

    fun transformedWidths(): List<Float> {
        return baseWidths.map { (it * scale).coerceIn(0.5f, 7f) }
    }
}

@Composable
private fun SignatureThumbnail(file: File, modifier: Modifier = Modifier) {
    val data = remember(file.path, file.lastModified()) { loadSignatureTemplate(file) }
    Canvas(modifier) {
        val strokesData = data?.first ?: return@Canvas
        val pts = strokesData.flatten()
        if (pts.isEmpty()) return@Canvas
        val minX = pts.minOf { it.x }; val maxX = pts.maxOf { it.x }
        val minY = pts.minOf { it.y }; val maxY = pts.maxOf { it.y }
        val pad = 6f
        val availW = size.width - 2f * pad
        val availH = size.height - 2f * pad
        val sc = minOf(availW / (maxX - minX).coerceAtLeast(1f), availH / (maxY - minY).coerceAtLeast(1f))
        val ox = pad + (availW - (maxX - minX) * sc) / 2f - minX * sc
        val oy = pad + (availH - (maxY - minY) * sc) / 2f - minY * sc
        strokesData.forEach { s ->
            drawPath(
                buildPathFromPoints(s.map { Offset(it.x * sc + ox, it.y * sc + oy) }),
                color = Color(0xFF1E3A8A),
                style = Stroke(width = 1.6f, cap = StrokeCap.Round, join = StrokeJoin.Round)
            )
        }
    }
}

@OptIn(ExperimentalComposeUiApi::class)
@Composable
fun DocSignScreen(
    pageBitmap: Bitmap?,
    documentId: String,
    statusMessage: String?,
    onApprove: (rawStrokes: List<List<Offset>>, rawWidths: List<Float>, canvasSize: IntSize, bmpWidth: Int, bmpHeight: Int) -> Unit
) {
    val strokes = remember { mutableStateListOf<MutableList<Offset>>() }
    var currentStrokePoints by remember { mutableStateOf<MutableList<Offset>?>(null) }
    val completedPaths = remember { mutableStateListOf<Path>() }
    var currentPath by remember { mutableStateOf<Path?>(null) }
    val completedWidths = remember { mutableStateListOf<Float>() }
    var strokeWidth by remember { mutableStateOf(1f) }
    val redoStack = remember { mutableStateListOf<Triple<MutableList<Offset>, Path, Float>>() }

    var floatingSig by remember { mutableStateOf<FloatingSignatureState?>(null) }

    val context = LocalContext.current
    var savedSignatureExists by remember { mutableStateOf(hasSavedSignature(context)) }
    var signatureActionMessage by remember { mutableStateOf<String?>(null) }
    var strokeTick by remember { mutableStateOf(0) }
    var outerBoxSize by remember { mutableStateOf(IntSize.Zero) }
    var canvasSize by remember { mutableStateOf(IntSize.Zero) }
    var zoom by remember { mutableStateOf(1f) }
    var panOffset by remember { mutableStateOf(Offset.Zero) }
    var showExecutionConfirmation by remember { mutableStateOf(false) }
    var showPdfDialog by remember { mutableStateOf(false) }

    var showSaveNameDialog by remember { mutableStateOf(false) }
    var saveNameText by remember { mutableStateOf("") }
    var showLoadDialog by remember { mutableStateOf(false) }
    var templateList by remember { mutableStateOf(listSignatureTemplates(context)) }
    var renamingTemplate by remember { mutableStateOf<SignatureTemplateInfo?>(null) }
    var renameText by remember { mutableStateOf("") }

    fun commitFloatingSignature() {
        val active = floatingSig ?: return
        val newStrokes = active.transformedStrokes()
        val newWidths = active.transformedWidths()
        newStrokes.forEachIndexed { idx, pts ->
            strokes.add(pts)
            completedPaths.add(buildPathFromPoints(pts))
            completedWidths.add(newWidths.getOrElse(idx) { 1f })
        }
        redoStack.clear()
        floatingSig = null
        strokeTick++
        signatureActionMessage = "Signature placed! You can add more strokes or send to plotter."
    }

    fun pageZoomStep(centroid: Offset, prevCentroid: Offset, zChange: Float) {
        val newZoom = (zoom * zChange).coerceIn(1f, 6f)
        val effectiveScale = newZoom / zoom
        val panDelta = centroid - prevCentroid
        val rawPan = centroid + (panOffset - centroid) * effectiveScale + panDelta

        if (newZoom <= 1.001f || canvasSize == IntSize.Zero) {
            zoom = 1f
            panOffset = Offset.Zero
            return
        }

        val extraMarginX = canvasSize.width * 0.65f
        val extraMarginY = canvasSize.height * 0.65f

        val minX = canvasSize.width - (canvasSize.width * newZoom) - extraMarginX
        val maxX = extraMarginX
        val minY = canvasSize.height - (canvasSize.height * newZoom) - extraMarginY
        val maxY = extraMarginY

        zoom = newZoom
        panOffset = Offset(
            rawPan.x.coerceIn(minX, maxX),
            rawPan.y.coerceIn(minY, maxY)
        )
    }

    fun clampToCanvas(o: Offset) = Offset(
        o.x.coerceIn(0f, canvasSize.width.toFloat()),
        o.y.coerceIn(0f, canvasSize.height.toFloat())
    )

    fun placeTemplate(info: SignatureTemplateInfo) {
        val loaded = loadSignatureTemplate(info.file)
        if (loaded == null) {
            signatureActionMessage = "Error loading “${info.displayName}”"
            return
        }
        if (floatingSig != null) commitFloatingSignature()

        val (loadedStrokes, loadedWidths, savedSize) = loaded
        val fit = if (savedSize.width > 0 && savedSize.height > 0 && canvasSize != IntSize.Zero) {
            minOf(
                canvasSize.width.toFloat() / savedSize.width.toFloat(),
                canvasSize.height.toFloat() / savedSize.height.toFloat()
            )
        } else 1f

        val scaledAll = loadedStrokes.map { pts -> pts.map { Offset(it.x * fit, it.y * fit) } }
        val allPts = scaledAll.flatten()
        if (allPts.isEmpty()) {
            signatureActionMessage = "“${info.displayName}” is empty"
            return
        }
        val minX = allPts.minOf { it.x }; val maxX = allPts.maxOf { it.x }
        val minY = allPts.minOf { it.y }; val maxY = allPts.maxOf { it.y }
        val cx = (minX + maxX) / 2f
        val cy = (minY + maxY) / 2f
        val centeredStrokes = scaledAll.map { stroke -> stroke.map { pt -> Offset(pt.x - cx, pt.y - cy) } }
        val scaledWidths = loadedStrokes.indices.map { i ->
            ((loadedWidths.getOrElse(i) { 1f }) * fit).coerceIn(0.5f, 7f)
        }

        val rawW = (maxX - minX).coerceAtLeast(10f)
        val rawH = (maxY - minY).coerceAtLeast(10f)

        val targetWidth = if (canvasSize.width > 0) (canvasSize.width * 0.26f).coerceIn(100f, 300f) else 200f
        val initScale = (targetWidth / rawW).coerceIn(0.1f, 3.0f)

        val target = if (canvasSize != IntSize.Zero) {
            clampToCanvas(Offset(
                (canvasSize.width / 2f - panOffset.x) / zoom,
                (canvasSize.height / 2f - panOffset.y) / zoom
            ))
        } else Offset(200f, 200f)

        floatingSig = FloatingSignatureState(
            baseStrokes = centeredStrokes,
            baseWidths = scaledWidths,
            baseWidth = rawW,
            baseHeight = rawH,
            initialCenter = target,
            initialScale = initScale
        )
        signatureActionMessage = "Loaded “${info.displayName}” — drag to move, pinch or drag a corner to resize, then tap ✓ Stamp"
    }

    Column(Modifier.fillMaxSize().padding(horizontal = 6.dp, vertical = 3.dp)) {
        Box(
            modifier = Modifier
                .weight(1f)
                .fillMaxWidth()
                .shadow(6.dp, RoundedCornerShape(12.dp))
                .clip(RoundedCornerShape(12.dp))
                .background(Color(0xFFE2E8F0))
                .onSizeChanged { outerBoxSize = it }
                .pointerInput(floatingSig != null) {
                    awaitEachGesture {
                        var initialEvent: androidx.compose.ui.input.pointer.PointerEvent? = null
                        var firstDown: androidx.compose.ui.input.pointer.PointerInputChange? = null
                        while (firstDown == null) {
                            val ev = awaitPointerEvent()
                            firstDown = ev.changes.firstOrNull { it.pressed }
                            if (firstDown != null) initialEvent = ev
                        }
                        val down = firstDown!!
                        val initialPressed = initialEvent!!.changes.filter { it.pressed }

                        // A button / toolbar already handled this touch.
                        if (down.isConsumed) {
                            do {
                                val e = awaitPointerEvent()
                            } while (e.changes.any { it.pressed })
                            return@awaitEachGesture
                        }

                        // Pointer positions here are in the fixed (un-zoomed) outer box. These two
                        // helpers map them into the page box / page canvas using the CURRENT zoom
                        // state, so zoom and pan track the fingers exactly (no feedback lag).
                        val fo = Offset(
                            (outerBoxSize.width - canvasSize.width) / 2f,
                            (outerBoxSize.height - canvasSize.height) / 2f
                        )
                        fun rel(p: Offset): Offset = p - fo
                        fun toCanvas(p: Offset): Offset =
                            Offset((p.x - fo.x - panOffset.x) / zoom, (p.y - fo.y - panOffset.y) / zoom)

                        val activeFloating = floatingSig
                        if (activeFloating != null) {
                            val handleRadius = 46f / zoom
                            val downC = toCanvas(down.position)
                            var activeCorner = -1
                            if (initialPressed.size == 1) {
                                var bestDist = handleRadius
                                for (ci in 0..3) {
                                    val d = (downC - activeFloating.cornerPos(ci)).getDistance()
                                    if (d <= bestDist) { bestDist = d; activeCorner = ci }
                                }
                            }
                            val anchor = if (activeCorner >= 0) activeFloating.cornerPos(3 - activeCorner) else Offset.Zero
                            val startDist = (downC - anchor).getDistance().coerceAtLeast(1f)
                            val startScale = activeFloating.scale
                            val startCenterVec = activeFloating.center - anchor

                            var lastCount = initialPressed.size
                            var pinchOnSignature: Boolean? = null
                            var prevCentroid = initialPressed.map { it.position }.reduce { a, b -> a + b } / initialPressed.size.toFloat()
                            var prevAvgDist = if (initialPressed.size >= 2) {
                                initialPressed.map { (it.position - prevCentroid).getDistance() }.average().toFloat()
                            } else 0f

                            initialPressed.forEach { it.consume() }

                            while (true) {
                                val event = awaitPointerEvent()
                                val pressed = event.changes.filter { it.pressed }
                                if (pressed.isEmpty()) break
                                pressed.forEach { it.consume() }

                                val centroid = pressed.map { it.position }.reduce { a, b -> a + b } / pressed.size.toFloat()
                                if (pressed.size != lastCount) {
                                    lastCount = pressed.size
                                    prevCentroid = centroid
                                    prevAvgDist = if (pressed.size >= 2) {
                                        pressed.map { (it.position - centroid).getDistance() }.average().toFloat()
                                    } else 0f
                                    if (pressed.size < 2) pinchOnSignature = null
                                    continue
                                }

                                if (pressed.size >= 2) {
                                    val avgDist = pressed.map { (it.position - centroid).getDistance() }.average().toFloat()
                                    val factor = if (prevAvgDist > 1f && avgDist > 1f) avgDist / prevAvgDist else 1f
                                    if (pinchOnSignature == null) {
                                        pinchOnSignature = activeFloating.contains(toCanvas(centroid), 40f / zoom)
                                    }
                                    if (pinchOnSignature == true) {
                                        activeFloating.scale = (activeFloating.scale * factor).coerceIn(0.15f, 6f)
                                        activeFloating.center = clampToCanvas(activeFloating.center + (centroid - prevCentroid) / zoom)
                                    } else {
                                        pageZoomStep(rel(centroid), rel(prevCentroid), factor)
                                    }
                                    prevCentroid = centroid
                                    prevAvgDist = avgDist
                                } else {
                                    val pos = pressed.first().position
                                    if (activeCorner >= 0) {
                                        val newScale = (startScale * (toCanvas(pos) - anchor).getDistance() / startDist).coerceIn(0.15f, 6f)
                                        activeFloating.scale = newScale
                                        activeFloating.center = clampToCanvas(anchor + startCenterVec * (newScale / startScale))
                                    } else {
                                        activeFloating.center = clampToCanvas(activeFloating.center + (pos - prevCentroid) / zoom)
                                    }
                                    prevCentroid = pos
                                }
                                strokeTick++
                            }
                            return@awaitEachGesture
                        }

                        val widthForThisStroke = strokeWidth
                        var isPanZoom = initialPressed.size >= 2
                        var prevCentroid: Offset
                        var prevAvgDist: Float

                        if (isPanZoom) {
                            initialPressed.forEach { it.consume() }
                            prevCentroid = initialPressed.map { it.position }.reduce { a, b -> a + b } / initialPressed.size.toFloat()
                            prevAvgDist = initialPressed.map { (it.position - prevCentroid).getDistance() }.average().toFloat()
                        } else {
                            down.consume()
                            val p0 = clampToCanvas(toCanvas(down.position))
                            currentStrokePoints = mutableListOf(p0)
                            currentPath = Path().apply { moveTo(p0.x, p0.y) }
                            strokeTick++
                            prevCentroid = down.position
                            prevAvgDist = 0f
                        }

                        while (true) {
                            val event = awaitPointerEvent()
                            val pressed = event.changes.filter { it.pressed }

                            if (pressed.isEmpty()) {
                                if (!isPanZoom) {
                                    currentStrokePoints?.let { strokes.add(it) }
                                    currentPath?.let { completedPaths.add(it) }
                                    completedWidths.add(widthForThisStroke)
                                    redoStack.clear()
                                }
                                currentStrokePoints = null
                                currentPath = null
                                strokeTick++
                                break
                            }

                            if (!isPanZoom && pressed.size >= 2) {
                                isPanZoom = true
                                currentStrokePoints = null
                                currentPath = null
                                strokeTick++
                                prevCentroid = pressed.map { it.position }.reduce { a, b -> a + b } / pressed.size.toFloat()
                                prevAvgDist = pressed.map { (it.position - prevCentroid).getDistance() }.average().toFloat()
                                pressed.forEach { it.consume() }
                                continue
                            }

                            if (isPanZoom) {
                                pressed.forEach { it.consume() }
                                val centroid = pressed.map { it.position }.reduce { a, b -> a + b } / pressed.size.toFloat()
                                val avgDist = pressed.map { (it.position - centroid).getDistance() }.average().toFloat()
                                val zChange = if (prevAvgDist > 1f && avgDist > 1f) (avgDist / prevAvgDist) else 1f
                                pageZoomStep(rel(centroid), rel(prevCentroid), zChange)
                                prevCentroid = centroid
                                prevAvgDist = avgDist
                            } else {
                                val change = pressed.firstOrNull { it.id == down.id } ?: pressed.first()
                                change.consume()
                                var added = false
                                val samples = change.historical.map { it.position } + change.position
                                for (rawPoint in samples) {
                                    val newPoint = clampToCanvas(toCanvas(rawPoint))
                                    val prev = currentStrokePoints?.lastOrNull()
                                    if (prev == null || (newPoint - prev).getDistance() >= 0.4f) {
                                        currentStrokePoints?.add(newPoint)
                                        if (prev != null) {
                                            val midX = (prev.x + newPoint.x) / 2f
                                            val midY = (prev.y + newPoint.y) / 2f
                                            currentPath?.quadraticBezierTo(prev.x, prev.y, midX, midY)
                                        }
                                        added = true
                                    }
                                }
                                if (added) strokeTick++
                            }
                        }
                    }
                },
            contentAlignment = Alignment.Center
        ) {
            if (pageBitmap != null && outerBoxSize != IntSize.Zero) {
                val imgAspect = pageBitmap.width.toFloat() / pageBitmap.height.toFloat()
                val boxAspect = outerBoxSize.width.toFloat() / outerBoxSize.height.toFloat()
                val fittedW: Int
                val fittedH: Int
                if (imgAspect > boxAspect) {
                    fittedW = outerBoxSize.width
                    fittedH = (outerBoxSize.width / imgAspect).roundToInt()
                } else {
                    fittedH = outerBoxSize.height
                    fittedW = (outerBoxSize.height * imgAspect).roundToInt()
                }

                val density = LocalContext.current.resources.displayMetrics.density

                Box(
                    Modifier
                        .size((fittedW / density).dp, (fittedH / density).dp)
                        .graphicsLayer {
                            scaleX = zoom
                            scaleY = zoom
                            translationX = panOffset.x
                            translationY = panOffset.y
                            transformOrigin = TransformOrigin(0f, 0f)
                        }
                        .clip(RectangleShape)
                        .background(Color.White)
                ) {
                    Image(
                        bitmap = remember(pageBitmap) { pageBitmap.asImageBitmap() },
                        contentDescription = "Document page",
                        contentScale = ContentScale.FillBounds,
                        modifier = Modifier.fillMaxSize()
                    )

                    Canvas(
                        modifier = Modifier
                            .fillMaxSize()
                            .onSizeChanged { canvasSize = it }
                    ) {
                        @Suppress("UNUSED_EXPRESSION")
                        strokeTick

                        completedPaths.forEachIndexed { i, p ->
                            val width = completedWidths.getOrElse(i) { 1f }
                            drawPath(p, color = Color(0xFF1E3A8A), style = Stroke(width = width, cap = StrokeCap.Round, join = StrokeJoin.Round))
                        }
                        currentPath?.let { p ->
                            drawPath(p, color = Color(0xFF1E3A8A), style = Stroke(width = strokeWidth, cap = StrokeCap.Round, join = StrokeJoin.Round))
                        }

                        floatingSig?.let { fs ->
                            val previewStrokes = fs.transformedStrokes()
                            val previewWidths = fs.transformedWidths()
                            previewStrokes.forEachIndexed { idx, pts ->
                                val p = buildPathFromPoints(pts)
                                drawPath(
                                    p,
                                    color = Color(0xFF1D4ED8),
                                    style = Stroke(width = previewWidths.getOrElse(idx) { 1f }, cap = StrokeCap.Round, join = StrokeJoin.Round)
                                )
                            }

                            val zr = 1f / zoom
                            val boxW = fs.boxW
                            val boxH = fs.boxH
                            val topLeft = Offset(fs.center.x - boxW / 2f, fs.center.y - boxH / 2f)

                            drawRect(
                                color = Color(0xFF2563EB).copy(alpha = 0.08f),
                                topLeft = topLeft,
                                size = Size(boxW, boxH)
                            )
                            drawRect(
                                color = Color(0xFF2563EB),
                                topLeft = topLeft,
                                size = Size(boxW, boxH),
                                style = Stroke(
                                    width = 2.5f * zr,
                                    pathEffect = PathEffect.dashPathEffect(floatArrayOf(12f * zr, 8f * zr), 0f)
                                )
                            )

                            for (cIdx in 0..3) {
                                val cPos = fs.cornerPos(cIdx)
                                drawCircle(color = Color.White, radius = 13f * zr, center = cPos)
                                drawCircle(color = Color(0xFF2563EB), radius = 9.5f * zr, center = cPos)
                            }
                        }
                    }
                }

                if (floatingSig != null) {
                    Surface(
                        color = Color(0xFF1E293B).copy(alpha = 0.92f),
                        shape = RoundedCornerShape(50),
                        shadowElevation = 8.dp,
                        modifier = Modifier
                            .align(Alignment.TopCenter)
                            .padding(top = 10.dp)
                    ) {
                        Row(
                            modifier = Modifier.padding(horizontal = 12.dp, vertical = 4.dp),
                            verticalAlignment = Alignment.CenterVertically,
                            horizontalArrangement = Arrangement.spacedBy(8.dp)
                        ) {
                            Text(
                                "Drag to move · Pinch/Corner to resize",
                                color = Color.White,
                                fontSize = 11.sp
                            )
                            Button(
                                onClick = { commitFloatingSignature() },
                                contentPadding = PaddingValues(horizontal = 10.dp, vertical = 2.dp),
                                modifier = Modifier.height(28.dp),
                                colors = ButtonDefaults.buttonColors(containerColor = Color(0xFF10B981))
                            ) {
                                Text("✓ Stamp", fontSize = 12.sp, fontWeight = FontWeight.Bold)
                            }
                            TextButton(
                                onClick = { floatingSig = null },
                                contentPadding = PaddingValues(horizontal = 6.dp, vertical = 2.dp),
                                modifier = Modifier.height(28.dp)
                            ) {
                                Text("✕", color = Color(0xFFFCA5A5), fontSize = 13.sp, fontWeight = FontWeight.Bold)
                            }
                        }
                    }
                }
                if (zoom > 1.05f) {
                    Surface(
                        color = Color.Black.copy(alpha = 0.55f),
                        shape = RoundedCornerShape(50),
                        modifier = Modifier.align(Alignment.BottomStart).padding(8.dp)
                    ) {
                        TextButton(
                            contentPadding = PaddingValues(horizontal = 10.dp, vertical = 0.dp),
                            modifier = Modifier.height(28.dp),
                            onClick = { zoom = 1f; panOffset = Offset.Zero }
                        ) {
                            Text("Reset zoom (${String.format("%.1f", zoom)}x)", fontSize = 11.sp, color = Color(0xFF93C5FD))
                        }
                    }
                }
            } else {
                Text("No Document Loaded", color = Color.Gray)
            }
        }

        Spacer(Modifier.height(4.dp))

        Row(
            Modifier.fillMaxWidth().height(32.dp).padding(horizontal = 4.dp),
            verticalAlignment = Alignment.CenterVertically
        ) {
            Text("Pen", style = MaterialTheme.typography.labelMedium, fontWeight = FontWeight.SemiBold)
            Slider(
                value = strokeWidth,
                onValueChange = { strokeWidth = it },
                valueRange = 0.5f..7f,
                colors = SliderDefaults.colors(thumbColor = MaterialTheme.colorScheme.primary, activeTrackColor = MaterialTheme.colorScheme.secondary),
                modifier = Modifier.weight(1f).padding(horizontal = 8.dp)
            )
            Text(String.format("%.1f", strokeWidth), style = MaterialTheme.typography.labelSmall)
        }

        // The scanned page with the current signature strokes burned in (used by Download PDF and Share).
        class SignedPage(val bitmap: Bitmap, val strokes: List<List<Offset>>, val widths: List<Float>)
        fun buildSignedPage(): SignedPage? {
            val bmp = pageBitmap ?: return null
            val sx = if (canvasSize.width > 0) bmp.width.toFloat() / canvasSize.width.toFloat() else 1f
            val sy = if (canvasSize.height > 0) bmp.height.toFloat() / canvasSize.height.toFloat() else 1f
            val allStrokes = strokes.map { it.toList() } + (floatingSig?.transformedStrokes() ?: emptyList())
            val allWidths = completedWidths.toList() + (floatingSig?.transformedWidths() ?: emptyList())
            val pageStrokes = allStrokes.map { st -> st.map { Offset(it.x * sx, it.y * sy) } }
            val pageWidths = allWidths.map { it * (sx + sy) / 2f }
            return SignedPage(bmp, pageStrokes, pageWidths)   // strokes stay vectors in the PDF
        }

        if (showPdfDialog) {
            PdfNameDialog(
                defaultName = defaultPdfName("DocSign"),
                onDismiss = { showPdfDialog = false },
                onDownload = { n ->
                    buildSignedPage()?.let { sp ->
                        signatureActionMessage = saveBitmapAsPdf(context, sp.bitmap, n, sp.strokes, sp.widths) ?: "Failed to save PDF"
                    }
                },
                onShare = { n ->
                    buildSignedPage()?.let { sp ->
                        signatureActionMessage = shareBitmapAsPdf(context, sp.bitmap, n, sp.strokes, sp.widths) ?: "Failed to share document"
                    }
                }
            )
        }

        Row(
            Modifier.fillMaxWidth(),
            horizontalArrangement = Arrangement.SpaceBetween,
            verticalAlignment = Alignment.CenterVertically
        ) {
            IconButton(
                modifier = Modifier.size(36.dp),
                enabled = strokes.isNotEmpty() || floatingSig != null,
                onClick = {
                    if (floatingSig != null) {
                        floatingSig = null
                    } else if (strokes.isNotEmpty()) {
                        val lastPoints = strokes.removeAt(strokes.lastIndex)
                        val lastPath = completedPaths.removeAt(completedPaths.lastIndex)
                        val lastWidth = completedWidths.removeAt(completedWidths.lastIndex)
                        redoStack.add(Triple(lastPoints, lastPath, lastWidth))
                    }
                }
            ) {
                Icon(Icons.AutoMirrored.Filled.Undo, contentDescription = "Undo")
            }

            IconButton(
                modifier = Modifier.size(36.dp),
                enabled = redoStack.isNotEmpty(),
                onClick = {
                    val (points, path, width) = redoStack.removeAt(redoStack.lastIndex)
                    strokes.add(points)
                    completedPaths.add(path)
                    completedWidths.add(width)
                }
            ) {
                Icon(Icons.AutoMirrored.Filled.Redo, contentDescription = "Redo")
            }

            IconButton(
                modifier = Modifier.size(36.dp),
                onClick = {
                    strokes.clear(); completedPaths.clear(); completedWidths.clear(); redoStack.clear()
                    currentStrokePoints = null; currentPath = null; floatingSig = null
                }
            ) {
                Icon(Icons.Default.Delete, contentDescription = "Clear All", tint = MaterialTheme.colorScheme.error)
            }

            IconButton(
                modifier = Modifier.size(36.dp),
                enabled = strokes.isNotEmpty() || floatingSig != null,
                onClick = {
                    if (floatingSig != null) commitFloatingSignature()
                    templateList = listSignatureTemplates(context)
                    saveNameText = "Signature ${templateList.size + 1}"
                    showSaveNameDialog = true
                }
            ) {
                Icon(Icons.Default.BookmarkAdd, contentDescription = "Save Signature", tint = MaterialTheme.colorScheme.primary)
            }

            IconButton(
                modifier = Modifier.size(36.dp),
                enabled = pageBitmap != null,
                onClick = { showPdfDialog = true }
            ) {
                Icon(Icons.Default.PictureAsPdf, contentDescription = "Download PDF", tint = MaterialTheme.colorScheme.secondary)
            }

            IconButton(
                modifier = Modifier.size(36.dp),
                enabled = pageBitmap != null,
                onClick = { showPdfDialog = true }
            ) {
                Icon(Icons.Default.Share, contentDescription = "Share document", tint = MaterialTheme.colorScheme.primary)
            }

            Surface(
                shape = RoundedCornerShape(20.dp),
                color = if (savedSignatureExists) MaterialTheme.colorScheme.primaryContainer else MaterialTheme.colorScheme.surfaceVariant,
                modifier = Modifier
                    .height(38.dp)
                    .clickable(enabled = savedSignatureExists) {
                        templateList = listSignatureTemplates(context)
                        showLoadDialog = true
                    }
            ) {
                Row(
                    modifier = Modifier.padding(horizontal = 8.dp),
                    verticalAlignment = Alignment.CenterVertically,
                    horizontalArrangement = Arrangement.spacedBy(4.dp)
                ) {
                    Icon(
                        Icons.Default.FolderSpecial,
                        contentDescription = null,
                        modifier = Modifier.size(18.dp),
                        tint = if (savedSignatureExists) MaterialTheme.colorScheme.onPrimaryContainer else MaterialTheme.colorScheme.onSurfaceVariant
                    )
                    Text(
                        "Saved Signs",
                        fontSize = 12.sp,
                        fontWeight = FontWeight.SemiBold,
                        color = if (savedSignatureExists) MaterialTheme.colorScheme.onPrimaryContainer else MaterialTheme.colorScheme.onSurfaceVariant
                    )
                }
            }
        }

        Spacer(Modifier.height(6.dp))

        Button(
            enabled = pageBitmap != null && (strokes.isNotEmpty() || floatingSig != null) && canvasSize != IntSize.Zero,
            modifier = Modifier.fillMaxWidth().height(46.dp),
            shape = RoundedCornerShape(12.dp),
            onClick = {
                if (floatingSig != null) commitFloatingSignature()
                showExecutionConfirmation = true
            }
        ) { Text("Review & Send to Plotter", fontSize = 15.sp, fontWeight = FontWeight.Bold) }

        val displayMsg = signatureActionMessage ?: statusMessage
        if (displayMsg != null) {
            Text(
                text = displayMsg,
                modifier = Modifier.fillMaxWidth().padding(top = 4.dp),
                style = MaterialTheme.typography.labelSmall,
                color = MaterialTheme.colorScheme.primary,
                maxLines = 1
            )
        }
    }

    if (showExecutionConfirmation) {
        AlertDialog(
            onDismissRequest = { showExecutionConfirmation = false },
            title = { Text("Send this signature?") },
            text = {
                Text(
                    "The host will draw the strokes from the toolhead’s current connect-time origin. " +
                            "Check that the page is aligned, the pen is clear, and the live camera view is upright."
                )
            },
            confirmButton = {
                Button(onClick = {
                    showExecutionConfirmation = false
                    pageBitmap?.let { bmp ->
                        val rawStrokes = strokes.map { it.toList() }.toList()
                        val rawWidths = completedWidths.toList()
                        onApprove(rawStrokes, rawWidths, canvasSize, bmp.width, bmp.height)
                    }
                }) {
                    Text("Send to plotter")
                }
            },
            dismissButton = {
                TextButton(onClick = { showExecutionConfirmation = false }) {
                    Text("Keep editing")
                }
            }
        )
    }

    if (showSaveNameDialog) {
        AlertDialog(
            onDismissRequest = { showSaveNameDialog = false },
            title = { Text("Save Signature Template") },
            text = {
                OutlinedTextField(
                    value = saveNameText,
                    onValueChange = { saveNameText = it },
                    singleLine = true,
                    label = { Text("Signature Name") },
                    modifier = Modifier.fillMaxWidth()
                )
            },
            confirmButton = {
                Button(onClick = {
                    saveSignatureTemplate(context, saveNameText, strokes.toList(), completedWidths.toList(), canvasSize)
                    templateList = listSignatureTemplates(context)
                    savedSignatureExists = true
                    signatureActionMessage = "Saved as “${saveNameText.trim().ifBlank { "Signature" }}”"
                    showSaveNameDialog = false
                }) { Text("Save") }
            },
            dismissButton = {
                TextButton(onClick = { showSaveNameDialog = false }) { Text("Cancel") }
            }
        )
    }

    if (showLoadDialog) {
        AlertDialog(
            onDismissRequest = { showLoadDialog = false },
            title = { Text("Saved Signatures") },
            text = {
                if (templateList.isEmpty()) {
                    Text("No saved signatures yet.")
                } else {
                    Column(
                        Modifier
                            .fillMaxWidth()
                            .heightIn(max = 420.dp)
                            .verticalScroll(rememberScrollState()),
                        verticalArrangement = Arrangement.spacedBy(8.dp)
                    ) {
                        Text(
                            "Tap a signature to place it on the page. Then drag to move, pinch or drag a corner to resize, and tap ✓ Stamp.",
                            fontSize = 12.sp,
                            color = MaterialTheme.colorScheme.onSurfaceVariant
                        )
                        templateList.forEach { info ->
                            Row(
                                Modifier.fillMaxWidth(),
                                verticalAlignment = Alignment.CenterVertically,
                                horizontalArrangement = Arrangement.spacedBy(8.dp)
                            ) {
                                SignatureThumbnail(
                                    file = info.file,
                                    modifier = Modifier
                                        .size(width = 92.dp, height = 52.dp)
                                        .clip(RoundedCornerShape(8.dp))
                                        .background(Color.White)
                                        .border(1.dp, Color(0xFFCBD5E1), RoundedCornerShape(8.dp))
                                        .clickable {
                                            placeTemplate(info)
                                            showLoadDialog = false
                                        }
                                )
                                Text(
                                    info.displayName,
                                    fontWeight = FontWeight.Medium,
                                    maxLines = 2,
                                    modifier = Modifier
                                        .weight(1f)
                                        .clickable {
                                            placeTemplate(info)
                                            showLoadDialog = false
                                        }
                                )
                                Column(horizontalAlignment = Alignment.End) {
                                    TextButton(
                                        contentPadding = PaddingValues(horizontal = 6.dp, vertical = 0.dp),
                                        modifier = Modifier.height(30.dp),
                                        onClick = {
                                            renamingTemplate = info
                                            renameText = info.displayName
                                        }
                                    ) {
                                        Text("Rename", color = MaterialTheme.colorScheme.secondary, fontSize = 13.sp)
                                    }
                                    TextButton(
                                        contentPadding = PaddingValues(horizontal = 6.dp, vertical = 0.dp),
                                        modifier = Modifier.height(30.dp),
                                        onClick = {
                                            deleteSignatureTemplate(info.file)
                                            templateList = listSignatureTemplates(context)
                                            savedSignatureExists = templateList.isNotEmpty()
                                            if (templateList.isEmpty()) showLoadDialog = false
                                        }
                                    ) {
                                        Text("Delete", color = MaterialTheme.colorScheme.error, fontSize = 13.sp)
                                    }
                                }
                            }
                        }
                    }
                }
            },
            confirmButton = {
                TextButton(onClick = { showLoadDialog = false }) { Text("Close") }
            }
        )
    }

    if (renamingTemplate != null) {
        val targetInfo = renamingTemplate!!
        AlertDialog(
            onDismissRequest = { renamingTemplate = null },
            title = { Text("Rename Signature") },
            text = {
                OutlinedTextField(
                    value = renameText,
                    onValueChange = { renameText = it },
                    singleLine = true,
                    label = { Text("New Name") },
                    modifier = Modifier.fillMaxWidth()
                )
            },
            confirmButton = {
                Button(onClick = {
                    val ok = renameSignatureTemplate(context, targetInfo.file, renameText)
                    if (ok) {
                        templateList = listSignatureTemplates(context)
                        signatureActionMessage = "Renamed to “${renameText.trim().ifBlank { "Signature" }}”"
                    }
                    renamingTemplate = null
                }) { Text("Save Name") }
            },
            dismissButton = {
                TextButton(onClick = { renamingTemplate = null }) { Text("Cancel") }
            }
        )
    }
}

private fun warpDocument(source: Bitmap, corners: List<Offset>): Bitmap {
    val (tl, tr, br, bl) = corners
    fun distance(a: Offset, b: Offset): Float {
        val dx = a.x - b.x
        val dy = a.y - b.y
        return kotlin.math.sqrt(dx * dx + dy * dy)
    }

    val outWidth = maxOf(distance(tl, tr), distance(bl, br)).toInt().coerceAtLeast(1)
    val outHeight = maxOf(distance(tl, bl), distance(tr, br)).toInt().coerceAtLeast(1)

    val src = floatArrayOf(tl.x, tl.y, tr.x, tr.y, br.x, br.y, bl.x, bl.y)
    val dst = floatArrayOf(0f, 0f, outWidth.toFloat(), 0f, outWidth.toFloat(), outHeight.toFloat(), 0f, outHeight.toFloat())

    val matrix = android.graphics.Matrix()
    matrix.setPolyToPoly(src, 0, dst, 0, 4)

    val output = Bitmap.createBitmap(outWidth, outHeight, Bitmap.Config.ARGB_8888)
    val canvas = AndroidCanvas(output)
    val paint = Paint(Paint.ANTI_ALIAS_FLAG or Paint.FILTER_BITMAP_FLAG)

    val contrast = 1.25f
    val brightness = -12f
    paint.colorFilter = android.graphics.ColorMatrixColorFilter(
        android.graphics.ColorMatrix(
            floatArrayOf(
                contrast, 0f, 0f, 0f, brightness,
                0f, contrast, 0f, 0f, brightness,
                0f, 0f, contrast, 0f, brightness,
                0f, 0f, 0f, 1f, 0f
            )
        )
    )

    canvas.drawBitmap(source, matrix, paint)
    return output
}

private fun renderDoodleOnly(
    strokes: List<List<Offset>>,
    strokeWidths: List<Float>,
    pageWidth: Int,
    pageHeight: Int
): Bitmap {
    val result = Bitmap.createBitmap(pageWidth, pageHeight, Bitmap.Config.ARGB_8888)
    result.eraseColor(AndroidColor.TRANSPARENT)
    val canvas = AndroidCanvas(result)
    val paint = Paint().apply {
        color = AndroidColor.BLUE
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
        isAntiAlias = true
    }

    strokes.forEachIndexed { strokeIndex, stroke ->
        paint.strokeWidth = strokeWidths.getOrElse(strokeIndex) { 1f }
        for (i in 0 until stroke.size - 1) {
            canvas.drawLine(
                stroke[i].x, stroke[i].y,
                stroke[i + 1].x, stroke[i + 1].y,
                paint
            )
        }
    }
    return result
}

private fun renderCompositePreview(
    basePage: Bitmap,
    strokes: List<List<Offset>>,
    strokeWidths: List<Float>
): Bitmap {
    val result = basePage.copy(Bitmap.Config.ARGB_8888, true)
    val canvas = AndroidCanvas(result)
    val paint = Paint().apply {
        color = AndroidColor.rgb(30, 58, 138)
        style = Paint.Style.STROKE
        strokeCap = Paint.Cap.ROUND
        strokeJoin = Paint.Join.ROUND
        isAntiAlias = true
    }

    strokes.forEachIndexed { strokeIndex, stroke ->
        paint.strokeWidth = (strokeWidths.getOrElse(strokeIndex) { 1f }).coerceAtLeast(2.0f)
        for (i in 0 until stroke.size - 1) {
            canvas.drawLine(
                stroke[i].x, stroke[i].y,
                stroke[i + 1].x, stroke[i + 1].y,
                paint
            )
        }
    }
    return result
}
