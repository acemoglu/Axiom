// swift-tools-version: 5.10

import PackageDescription

let package = Package(
    name: "Axiom",
    platforms: [
        .macOS(.v13),
        .iOS(.v16),
        .watchOS(.v9),
        .tvOS(.v16),
    ],
    products: [
        .library(
            name: "Axiom",
            targets: ["Axiom"]
        ),
    ],
    targets: [
        .target(
            name: "Axiom",
            swiftSettings: [
                .enableExperimentalFeature("StrictConcurrency"),
            ]
        ),
        .testTarget(
            name: "AxiomTests",
            dependencies: ["Axiom"],
            swiftSettings: [
                .enableExperimentalFeature("StrictConcurrency"),
            ]
        ),
    ]
)
