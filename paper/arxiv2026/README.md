# LeanNumBench arXiv Release

This directory is the public arXiv/preprint release package for
`LeanNumBench: Diagnosing LLM Proof Completion in Lean-Checked Numerical
Analysis`.

It is intentionally separate from venue-specific formatting. The arXiv files
here use a neutral article style.

## Build

```sh
latexmk -pdf main.tex
```

No model API calls are needed to build the PDFs or run the artifact smoke
check.

## Files

- `main.tex`: top-level arXiv source file.
- `appendix.tex`: appendix body loaded by `main.tex`.
- `references.bib`: bibliography database.
- `main.bbl`: bibliography generated from the bundled source.
- `figures/`: TikZ/PGFPlots figure sources loaded by `main.tex`.
- `anc/LeanNumBench_arxiv2026_release_artifact.zip`: arXiv ancillary
  reproducibility artifact.
- `release-notes.md`: release metadata.
