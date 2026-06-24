# LeanNumBench arXiv Release

This directory is the public arXiv/preprint release package for
`LeanNumBench: Diagnosing LLM Proof Completion in Lean-Checked Numerical
Analysis`.

It is intentionally separate from venue-specific formatting. The arXiv files
here use a neutral article style.

## Build

```powershell
latexmk -pdf main.tex
```

No model API calls are needed to build the PDFs or run the artifact smoke
check.

## Files

- `main.tex`, `main.pdf`: public preprint with appendix included.
- `appendix.tex`: appendix body loaded by `main.tex`.
- `anc/LeanNumBench_arxiv2026_release_artifact.zip`: arXiv ancillary
  reproducibility artifact.
- `release_artifact/`: path-sanitized public reproducibility artifact.
- `LeanNumBench_arxiv2026_source.zip`: TeX source bundle for arXiv upload.
- `LeanNumBench_arxiv2026_release_artifact.zip`: separate reproducibility
  artifact bundle.
