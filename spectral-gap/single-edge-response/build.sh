#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for task_document in main reading-guide; do
  for task_pass in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build "$task_document.tex" > "build/$task_document-pass-$task_pass.txt"
  done
done
cp build/main.pdf single-edge-response.pdf
cp build/reading-guide.pdf reading-guide.pdf
printf '%s\n' 'Built single-edge-response.pdf and reading-guide.pdf'
