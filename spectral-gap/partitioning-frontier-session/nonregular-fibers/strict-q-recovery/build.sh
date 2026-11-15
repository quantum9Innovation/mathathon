#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for source_file in \
  strict-q-blind-frame-recovery.tex \
  entropy-audit/strict-weight-entropy-gap.tex \
  support-audit/mixed-degree-small-support.tex \
  algorithm-audit/strict-q-algorithm-composition.tex
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
  strict-q-blind-frame-recovery.pdf \
  entropy-audit/strict-weight-entropy-gap.pdf \
  support-audit/mixed-degree-small-support.pdf \
  algorithm-audit/strict-q-algorithm-composition.pdf \
  strict-q-recovery-proof-packet.pdf
