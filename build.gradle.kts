plugins {
    kotlin("jvm") version "1.4.30" apply false
    id("org.sonarqube") version "3.1.1"
}

sonarqube {
    properties {
        property("sonar.projectKey", "wadoon_mini-symex")
        property("sonar.organization", "wadoon")
        property("sonar.host.url", "https://sonarcloud.io")        
        property("sonar.exclusions", "**/build/generated-src/antlr/main/**")
    }
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


