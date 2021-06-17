import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    java
    kotlin("jvm")
    antlr
    application
}

group = "edu.kit.formal.kastel"
version = "1.0-SNAPSHOT"

application {
    mainClass.set("edu.kit.iti.formal.MainKt")
}


val compileKotlin: KotlinCompile by tasks
compileKotlin.kotlinOptions.useIR = true
compileKotlin.dependsOn("generateGrammarSource")

repositories {
    mavenCentral()
}

dependencies {
    implementation("com.github.ajalt.clikt:clikt:3.1.0")
    implementation(kotlin("stdlib"))
    implementation("org.antlr:antlr4:4.8") // use ANTLR version 4
    antlr("org.antlr:antlr4:4.8") // use ANTLR version 4

    testImplementation("org.junit.jupiter:junit-jupiter-api:5.7.1")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine:5.7.1")
}

tasks.generateGrammarSource {
    inputs.file("$projectDir/src/main/antlr/TinyC.g4")
    inputs.file("$projectDir/src/main/antlr/MiniPascal.g4")
    inputs.file("$projectDir/src/main/antlr/SMTLIBv2.g4")

    maxHeapSize = "64m"
    arguments = arguments + listOf("-visitor", "-long-messages")
}

tasks.test {
    useJUnitPlatform()
}





