# LeanNumBench arXiv Release Notes

Release status: public preprint release package.

- Benchmark name: `LeanNumBench`.
- Author line: Qinghe Wang, Independent Researcher.
- Primary benchmark: 160 proof-completion records and 405 task specifications.
- Main evaluation: dated May-2026 five-endpoint proof-completion panel.
- Reproducibility: no paid API calls are required for PDF compilation or
  artifact smoke checks; model outputs are usage-stripped.
- License: CC-BY-4.0 for benchmark metadata; Apache-2.0 for companion Lean
  source, evaluation scripts, and release tooling.

Known limitations are stated in the paper and appendix: the release does not
yet include an independent taxonomy annotation study, Lean-feedback agent
baseline, full-160 pass@k panel, retrieval-augmented baseline,
shuffled/irrelevant-context control, or direct CAM-Bench numerical-subset rerun.

## Current Build Hashes

- Release artifact zip: `LeanNumBench_arxiv2026_release_artifact.zip`.
- arXiv ancillary artifact path: `anc/LeanNumBench_arxiv2026_release_artifact.zip`.
- Release artifact SHA256: `7c43bc13edfa1e4fd80dee535028f0553456dffb40d2ff67e7e293a9b19552d4`.
- Frozen 160-row proof prompt pack SHA256: `1271dbbde48bd5ab0a995df270547404468a3cd27330497f87fa9ae2bc881238`.
- Companion Lean `lake-manifest.json` SHA256: `2ed57a7e536783afef8fbb708429ea371e2524c941d8e7152f7a9bd3eca4b63b`.
- Public GitHub release:
  `https://github.com/Qinghev/LeanNumBench/releases/tag/v1.0-arxiv`.

