#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for source_file in \
  configuration-mixing-and-odd-blocks.tex \
  parity-reduction/nearconstant-configuration-atoms.tex \
  huang-primary/configuration-arbitrary-target-tails.tex \
  meszaros-extension/balanced-all-target-configuration.tex \
  parity-reduction/odd-blocks-degree-six-surgery.tex
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
  configuration-mixing-and-odd-blocks.pdf \
  parity-reduction/nearconstant-configuration-atoms.pdf \
  huang-primary/configuration-arbitrary-target-tails.pdf \
  meszaros-extension/balanced-all-target-configuration.pdf \
  configuration-proof-packet.pdf
