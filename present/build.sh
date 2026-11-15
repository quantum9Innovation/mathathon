#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$task_root"
export TEXINPUTS="$task_root/present/texmf/tex//:$task_root:${TEXINPUTS-}:"
export SOURCE_DATE_EPOCH=1794740400
mkdir -p present/report/build present/slides/build
build_target="${1:-all}"
case "$build_target" in
  all|report|slides) ;;
  *) printf 'Usage: bash present/build.sh [all|report|slides]\n' >&2; exit 2 ;;
esac
if [[ "$build_target" == all || "$build_target" == report ]]; then
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory=present/report/build -jobname=spectral-gap-report \
    spectral-gap-report.tex > "present/report/build/pass${pass}.txt"
done
cp present/report/build/spectral-gap-report.pdf spectral-gap-report.pdf
fi
if [[ "$build_target" == all || "$build_target" == slides ]]; then
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory=present/slides/build -jobname=spectral-gap-slides \
    spectral-gap-slides.tex > "present/slides/build/pass${pass}.txt"
done
cp present/slides/build/spectral-gap-slides.pdf spectral-gap-slides.pdf
fi
printf 'Built requested target: %s\n' "$build_target"
