#!/usr/bin/env bash
# Builds the C++ adapters for the fastted benchmark.
#
#   TREE_SIMILARITY_DIR  checkout of https://github.com/DatabaseGroup/tree-similarity at the 0.1.1 tag
#                        (git clone --branch 0.1.1 ...)
#   XTED_DIR             checkout of https://github.com/Davis-Fan/X-TED (no tagged release; default branch)
#   OUT                  output directory for the binaries (default: ./bin next to this script's parent
#                        scratch directory, which the caller should set)
#
# Release flags: -O3 -DNDEBUG. X-TED is compiled as C++14 with -pthread, as its own CMakeLists.txt does.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE_SIMILARITY_DIR:?set TREE_SIMILARITY_DIR to a tree-similarity checkout}"
: "${XTED_DIR:?set XTED_DIR to an X-TED checkout}"
: "${OUT:?set OUT to an output directory}"
mkdir -p "$OUT"

TS="$TREE_SIMILARITY_DIR/src"
TS_INCLUDES=()
for d in node label cost_model ted data_structures parser lookup lookup/scan lookup/index join join/naive \
         join/tjoin join/tang join/degree_histogram join/leaf_dist_histogram join/label_histogram \
         join/binary_branches join/histogram join/guha tree_generator ted_ub ted_lb json; do
  TS_INCLUDES+=("-I$TS/$d")
done

g++ -O3 -DNDEBUG -std=c++17 -Wall -Wno-unused-variable -I"$HERE" "${TS_INCLUDES[@]}" \
  "$HERE/tsim_adapter.cpp" -o "$OUT/tsim_adapter"

XTED_CPU="$XTED_DIR/X-TED_CPU"
g++ -O3 -DNDEBUG -std=c++14 -pthread -I"$HERE" -I"$XTED_CPU" \
  "$HERE/xted_adapter.cpp" "$XTED_CPU/TED.cpp" "$XTED_CPU/parallel_computing.cpp" \
  "$XTED_CPU/dataset_preprocess.cpp" -o "$OUT/xted_adapter"

echo "built $OUT/tsim_adapter and $OUT/xted_adapter"
