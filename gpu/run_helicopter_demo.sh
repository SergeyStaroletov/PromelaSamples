#!/bin/bash
# Helicopter Animation Demo for SPIN 2026 GPU Pipeline Artifact

set -e

echo "========================================="
echo "SPIN 2026: 3D Promela Demo"
echo "========================================="
echo "Author: Sergey Staroletov"
echo "Paper draft: Formal Modeling and Verification of Various GPU Pipeline Architectures in SPIN"
echo ""

if ! command -v spin &> /dev/null; then
    echo "ERROR: SPIN model checker is not installed!"
    exit 1
fi

mkdir -p output

echo "Generating animation frames by running pure Promela code (this may take some minutes)..."

spin -T gpu_no_pipeline.pml > output/heli_animation.txt

echo "Animation generation complete!"
echo ""
echo "Starting visualization..."

sleep 1

awk '/--- Frame/{system("sleep 0.1; clear")}/\|/{print;}' output/heli_animation.txt

