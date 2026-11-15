#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"
export TEXINPUTS="$repo_root/present/texmf/tex//:$repo_root:${TEXINPUTS-}:"
for doc in report-short report-long slides; do
  mkdir -p "present/build-$doc"
  for pass in 1 2 3; do
    pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error \
      -output-directory="present/build-$doc" "$doc.tex" > "present/build-$doc/pass$pass.txt"
  done
  cp "present/build-$doc/$doc.pdf" "$doc.pdf"
done
