plugins {
    kotlin("jvm") version "1.4.30" apply false
    id("org.sonarqube") version "3.1.1"
}
subprojects {
    group = "edu.kit.formal.kastel"
    version = "1.0-SNAPSHOT"

/*    tasks.withType(org.jetbrains.kotlin.gradle.tasks.KotlinCompile).all {
        kotlinOptions {
            suppressWarnings = false
            jvmTarget = "11"
        }
    }*/

    repositories {
        mavenCentral()
    }
}


