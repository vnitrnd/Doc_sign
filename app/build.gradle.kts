plugins {
    alias(libs.plugins.android.application)
    alias(libs.plugins.kotlin.compose)
}

// Supply these as environment variables on the build machine. Do not commit TURN credentials.
val turnUsername = System.getenv("DOCSIGN_TURN_USERNAME") ?: ""
val turnCredential = System.getenv("DOCSIGN_TURN_CREDENTIAL") ?: ""

android {
    namespace = "com.docsign.app"
    compileSdk = 35

    defaultConfig {
        applicationId = "com.docsign.app"
        minSdk = 24
        targetSdk = 35
        versionCode = 1
        versionName = "1.0"
        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        buildConfigField("String", "TURN_USERNAME", "\"$turnUsername\"")
        buildConfigField("String", "TURN_CREDENTIAL", "\"$turnCredential\"")
    }

    buildTypes {
        release {
            isMinifyEnabled = false
        }
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_11
        targetCompatibility = JavaVersion.VERSION_11
    }

    buildFeatures {
        compose = true
        buildConfig = true
    }
}

dependencies {
    // Material Design
    implementation(libs.material)

    // Google ML Kit Document Scanner UI (provided by Google Play services)
    implementation("com.google.android.gms:play-services-mlkit-document-scanner:16.0.0")

    // YouTube Player Android Library (retained from the existing project)
    implementation("com.pierfrancescosoffritti.androidyoutubeplayer:core:13.0.0")

    // OkHttp for backend communication
    implementation("com.squareup.okhttp3:okhttp:4.12.0")

    // WebRTC
    implementation("io.getstream:stream-webrtc-android:1.3.9")

    // Coroutines
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-android:1.8.1")

    // Core & Compose dependencies
    implementation(libs.androidx.core.ktx)
    implementation(libs.androidx.lifecycle.runtime.ktx)
    implementation(libs.androidx.lifecycle.runtime.compose)
    implementation(libs.androidx.activity.compose)
    implementation(platform(libs.androidx.compose.bom))
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.ui.graphics)
    implementation(libs.androidx.compose.ui.tooling.preview)
    implementation(libs.androidx.compose.material3)
    implementation("androidx.compose.material:material-icons-extended")

    testImplementation(libs.junit)
    androidTestImplementation(libs.androidx.junit)
    androidTestImplementation(libs.androidx.espresso.core)
    androidTestImplementation(platform(libs.androidx.compose.bom))
    androidTestImplementation(libs.androidx.compose.ui.test.junit4)
    debugImplementation(libs.androidx.compose.ui.tooling)
    debugImplementation(libs.androidx.compose.ui.test.manifest)
}
