#!/bin/bash
set -e

# This script is derived from the discussion in https://github.com/rust-fuzz/cargo-fuzz/issues/308

# Default values
OUTPUT_DIR="coverage"
TARGET_ARCH=""
FUZZ_TARGET=""

# Function to display help
show_help() {
    echo "Usage: $0 -t <fuzz_target> -a <target_arch> [-d <output_dir>]"
    echo ""
    echo "Options:"
    echo "  -t, --target       Fuzz target (required)"
    echo "  -a, --arch         Target architecture, e.g., x86_64-unknown-linux-gnu (required)"
    echo "  -d, --dir          Output directory for coverage reports (optional, default: coverage)"
    echo "  -h, --help         Display this help message"
}

# Parse command-line arguments
while [[ "$#" -gt 0 ]]; do
    case $1 in
        -t|--target) FUZZ_TARGET="$2"; shift ;;
        -a|--arch) TARGET_ARCH="$2"; shift ;;
        -d|--dir) OUTPUT_DIR="$2"; shift ;;
        -h|--help) show_help; exit 0 ;;
        *) echo "Unknown parameter passed: $1"; show_help; exit 1 ;;
    esac
    shift
done

# Check if mandatory arguments are provided
if [ -z "$FUZZ_TARGET" ] || [ -z "$TARGET_ARCH" ]; then
    echo "Error: fuzz_target and target_arch are required."
    show_help
    exit 1
fi

# Ensure necessary tools are installed
if ! command -v cargo &> /dev/null; then
    echo "Error: cargo could not be found, please install Rust and Cargo."
    exit 1
fi

if ! command -v llvm-cov &> /dev/null; then
    echo "Error: llvm-cov could not be found, please install LLVM."
    exit 1
fi

if ! command -v rustfilt &> /dev/null; then
    echo "Error: rustfilt could not be found, please install rustfilt."
    exit 1
fi

# Run the cargo fuzz coverage command with the provided fuzz target
cargo +nightly fuzz coverage "$FUZZ_TARGET"

# Define the paths
TARGET_DIR="target/${TARGET_ARCH}/coverage/${TARGET_ARCH}/release"
PROF_DATA="fuzz/coverage/$FUZZ_TARGET/coverage.profdata"

# Create the output directory if it doesn't exist
mkdir -p "$OUTPUT_DIR"

# Define output filenames based on the fuzz target
HTML_FILE="$OUTPUT_DIR/${FUZZ_TARGET}.coverage.html"

# Check if the coverage data file exists
if [ ! -f "$PROF_DATA" ]; then
    echo "Error: Coverage data file $PROF_DATA not found."
    exit 1
fi


# Generate the HTML report
llvm-cov show "$TARGET_DIR/$FUZZ_TARGET" --format=html \
                                         -Xdemangler=rustfilt \
                                         --ignore-filename-regex="\.cargo" \
                                         --instr-profile="$PROF_DATA" \
                                         > "$HTML_FILE"

echo "Coverage reports generated:"
echo "  HTML: $HTML_FILE"
