#!/usr/bin/env bash

cd "$(dirname "$0")" || exit

for src in \
  ./ImplementationExample.agda \
  ./AnalysisFindingErrors/ListT.agda \
  ./AnalysisDec.agda \
  ./AnalysisPostulated/LawfulFunctorTuple₂.agda \
  ./AnalysisPostulated/LawfulApplicativeTuple₂.agda \
  ./AnalysisPostulated/LawfulMonadTuple₂.agda; do
  cabal run --project-dir .. agda2hs:agda2hs -- -v rp:100 "$src"
done
