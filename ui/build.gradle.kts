import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import java.net.URI

plugins {
    java
    kotlin("jvm")
    application
    id("org.openjfx.javafxplugin") version "0.0.9"
}

group = "edu.kit.formal.kastel"
version = "1.0-SNAPSHOT"


repositories {
    mavenCentral()
    jcenter()
    maven { url = URI("https://oss.sonatype.org/content/repositories/snapshots/") }
    maven { url = URI("https://dl.bintray.com/kordamp/maven") }
}


application {
    mainClass.set("edu.kit.iti.formal.MainKt")
}

val compileKotlin: KotlinCompile by tasks
compileKotlin.kotlinOptions.useIR = true

tasks.withType<org.jetbrains.kotlin.gradle.tasks.KotlinCompile>().all {
    kotlinOptions {
        suppressWarnings = false
        jvmTarget = "11"
    }
}

dependencies {
    implementation(project(":core"))
    implementation(kotlin("stdlib"))
    implementation("com.github.ajalt.clikt:clikt:3.1.0")
    implementation("org.fxmisc.richtext:richtextfx:0.10.5")
    implementation("org.kordamp.ikonli:ikonli-antdesignicons-pack:12.0.0")
    implementation("org.kordamp.ikonli:ikonli-fontawesome5-pack:12.0.0")
    implementation("org.kordamp.ikonli:ikonli-javafx:12.0.0")
    implementation("no.tornado:tornadofx:1.7.20")
}


javafx {
    version = "15.0.1"
    modules = listOf("javafx.web", "javafx.controls", "javafx.fxml", "javafx.swing")
}

