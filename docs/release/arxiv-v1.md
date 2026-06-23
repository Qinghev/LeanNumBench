# LeanNumBench arXiv v1 Release

Date: 2026-06-23

This release prepares LeanNumBench v1 as a public technical-report artifact.
It is formatted for public arXiv-style distribution rather than conference
submission.

## Files

- Paper source bundle: `paper/arxiv2026/LeanNumBench_arxiv2026_source.zip`
- Reproducibility artifact: `paper/arxiv2026/LeanNumBench_arxiv2026_release_artifact.zip`
- arXiv ancillary artifact path inside the source bundle:
  `anc/leannumbench-v1-artifact.zip`
- Top-level TeX file: `paper/arxiv2026/main.tex`
- Appendix input: `paper/arxiv2026/appendix.tex`

## No-API Checks

```bash
cd paper/arxiv2026
latexmk -pdf main.tex
cd release_artifact
python reproduction_scripts/artifact_smoke_check.py
```

The artifact smoke check should report:

```json
{
  "passed": true,
  "records": 160,
  "tasks": 405,
  "frontier_model_record_pairs": 800,
  "hard_subset_records": 11,
  "pass3_api_rows": 165
}
```

## Release Policy

Benchmark records, schemas, prompt packs, generated table data, and benchmark
metadata are released under CC-BY-4.0. Companion Lean source, evaluation
scripts, and release tooling are released under Apache-2.0.

Some frozen experiment files preserve legacy lowercase internal identifiers in
record names, prompt theorem placeholders, scratch-directory names, or coverage
table columns. These identifiers are part of the released experimental record;
the public paper and release name is LeanNumBench.

The development repository may contain historical notes and planning files.
For public use, the frozen v1 artifact under `paper/arxiv2026/release_artifact`
is the authoritative release object.
