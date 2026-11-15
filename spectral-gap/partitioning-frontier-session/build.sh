#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
for source_file in \
  normalized-resolvent-barrier.tex \
  higher-cheeger/markov-form-budget.tex \
  higher-cheeger/local-repair-obstruction.tex \
  higher-cheeger/inherited-repair-target.tex \
  dynamic-target/positive-offdiagonal-obstruction.tex
do
  output_dir="$(dirname -- "$source_file")"
  for pass in 1 2
  do
    pdflatex -interaction=nonstopmode -halt-on-error \
      -output-directory="$output_dir" "$source_file" >/dev/null
  done
done
