#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1794740400
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build -jobname=regular-community-recovery main.tex > build/main-pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build -jobname=regular-community-recovery main.tex > build/main-pass2.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build -jobname=regular-community-recovery main.tex > build/main-pass3.txt
cp build/regular-community-recovery.pdf regular-community-recovery.pdf
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build reading-guide.tex > build/guide-pass1.txt
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build reading-guide.tex > build/guide-pass2.txt
cp build/reading-guide.pdf reading-guide.pdf
(
  cd plain-language
  mkdir -p build
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build overview.tex > build/pass1.txt
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build overview.tex > build/pass2.txt
  cp build/overview.pdf results-explained.pdf
)
