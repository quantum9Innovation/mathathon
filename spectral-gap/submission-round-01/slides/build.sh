#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build renders
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build problem21-slides.tex > build/final-pass1.log 2>&1
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build problem21-slides.tex > build/final-pass2.log 2>&1
cp build/problem21-slides.pdf problem21-slides.pdf
pdftoppm -r 110 -png problem21-slides.pdf renders/slide > build/render.log 2>&1
pdftotext -layout problem21-slides.pdf build/slides-text.txt
pdfinfo problem21-slides.pdf > build/pdfinfo.txt
