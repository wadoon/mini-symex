import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    java
    kotlin("jvm") version "1.4.30"
    antlr
}

group = "org.example"
version = "1.0-SNAPSHOT"

//val compileKotlin: KotlinCompile by tasks
//compileKotlin.kotlinOptions.useIR = true

repositories {
    mavenCentral()
}

dependencies {
    implementation(kotlin("stdlib"))
    testCompile("junit", "junit", "4.12")
    implementation("org.antlr:antlr4:4.8") // use ANTLR version 4
    antlr("org.antlr:antlr4:4.8") // use ANTLR version 4
}

tasks.generateGrammarSource {
    maxHeapSize = "64m"
    arguments = arguments + listOf("-visitor", "-long-messages")
}
