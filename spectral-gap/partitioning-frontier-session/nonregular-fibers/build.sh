#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for source_file in \
  nonregular-fiber-counting-obstruction.tex \
  weighted-entropy/omission-weights-and-nonregular-entropy.tex \
  degree-refinement/color-masked-kernel-obstruction.tex \
  degree-refinement/degree-colored-positive-phase.tex
do
  output_dir="$(dirname -- "$source_file")"
  for pass in 1 2
  do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$output_dir" "$source_file" >/dev/null
  done
done
pdf_merge="${PDFUNITE:-pdfunite}"
"$pdf_merge" \
  nonregular-fiber-counting-obstruction.pdf \
  weighted-entropy/omission-weights-and-nonregular-entropy.pdf \
  degree-refinement/color-masked-kernel-obstruction.pdf \
  degree-refinement/degree-colored-positive-phase.pdf \
  nonregular-fibers-proof-packet.pdf
