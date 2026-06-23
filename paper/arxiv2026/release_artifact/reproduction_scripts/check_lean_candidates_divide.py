"""Incrementally check LeanNumBench proof candidates with divide-and-conquer batching.

`check_lean_candidate.py` is convenient for small files, but a large model
leaderboard can be slow when one failed candidate forces a full sequential
fallback. This runner first tries to compile batches, recursively splits only
the failing batches, and writes every resolved result to disk as soon as it is
known. Interrupted runs can therefore resume without losing completed checks.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any

import check_lean_candidate as harness


ROOT = Path(__file__).resolve().parents[1]


def candidate_key(item: dict[str, Any]) -> str:
    return f"{item.get('record_id')}::{item.get('candidate_id')}"


def result_key(result: dict[str, Any]) -> str:
    return f"{result.get('record_id')}::{result.get('candidate_id')}"


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            item = json.loads(line)
            if isinstance(item, dict):
                rows.append(item)
    return rows


def append_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")


def write_report(
    output: Path,
    rows_output: Path,
    lean_project: Path,
    ordered_keys: list[str],
    results_by_key: dict[str, dict[str, Any]],
) -> None:
    results = [results_by_key[key] for key in ordered_keys if key in results_by_key]
    payload = {
        "schema_version": "0.1.0",
        "report_kind": "lean_candidate_check",
        "lean_project": str(lean_project),
        "rows_output": str(rows_output.resolve()),
        "results": results,
        "passed": all(result["passed"] for result in results) if results else False,
        "summary": harness.summarize_results(results),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def timeout_failure(item: dict[str, Any], exc: subprocess.TimeoutExpired) -> dict[str, Any]:
    return {
        "record_id": item.get("record_id", "__unknown__"),
        "formal_file": "__unknown__",
        "mode": "proof_body_candidate",
        "candidate_id": item.get("candidate_id"),
        "contains_sorry": "sorry" in item.get("proof", ""),
        "batch_compiled": False,
        "repaired": False,
        "repair_steps": [],
        "passed": False,
        "returncode": None,
        "stdout": "",
        "stderr": str(exc),
    }


def value_failure(item: dict[str, Any], exc: ValueError) -> dict[str, Any]:
    return {
        "record_id": item.get("record_id", "__unknown__"),
        "formal_file": "__unknown__",
        "mode": "proof_body_candidate",
        "candidate_id": item.get("candidate_id"),
        "contains_sorry": "sorry" in item.get("proof", ""),
        "batch_compiled": False,
        "repaired": False,
        "repair_steps": [],
        "passed": False,
        "returncode": None,
        "stdout": "",
        "stderr": str(exc),
    }


def check_group(
    items: list[dict[str, Any]],
    lean_project: Path,
    timeout: int,
    repair_simple: bool,
) -> list[dict[str, Any]]:
    if not items:
        return []
    if len(items) == 1:
        item = items[0]
        try:
            return [harness.check_proof_candidate(item, lean_project, timeout, repair_simple)]
        except subprocess.TimeoutExpired as exc:
            return [timeout_failure(item, exc)]
        except ValueError as exc:
            return [value_failure(item, exc)]

    try:
        batch_results = harness.check_proof_candidates_batch(items, lean_project, timeout)
    except subprocess.TimeoutExpired:
        batch_results = None
    except ValueError:
        batch_results = None
    if batch_results is not None:
        return batch_results

    midpoint = len(items) // 2
    return [
        *check_group(items[:midpoint], lean_project, timeout, repair_simple),
        *check_group(items[midpoint:], lean_project, timeout, repair_simple),
    ]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-file", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rows-output", type=Path)
    parser.add_argument("--lean-project", type=Path, default=harness.DEFAULT_LEAN_PROJECT)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--chunk-size", type=int, default=10)
    parser.add_argument("--repair-simple", action="store_true")
    parser.add_argument("--resume", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    lean_project = args.lean_project.resolve()
    rows_output = args.rows_output or args.output.with_suffix(".rows.jsonl")
    candidates = harness.load_candidate_items(args.candidate_file)
    ordered_keys = [candidate_key(item) for item in candidates]

    results_by_key: dict[str, dict[str, Any]] = {}
    if args.resume:
        for row in load_jsonl(rows_output):
            results_by_key[result_key(row)] = row

    pending = [item for item in candidates if candidate_key(item) not in results_by_key]
    print(f"loaded={len(candidates)} done={len(results_by_key)} pending={len(pending)}", flush=True)

    def commit(rows: list[dict[str, Any]]) -> None:
        append_jsonl(rows_output, rows)
        for row in rows:
            results_by_key[result_key(row)] = row
        write_report(args.output, rows_output, lean_project, ordered_keys, results_by_key)
        passed = sum(1 for row in results_by_key.values() if row.get("passed"))
        print(f"checked={len(results_by_key)}/{len(candidates)} passed={passed}", flush=True)

    if not pending:
        write_report(args.output, rows_output, lean_project, ordered_keys, results_by_key)
        return 0

    # Check in moderate chunks so an interruption loses at most one chunk.
    chunk_size = max(1, args.chunk_size)
    for start in range(0, len(pending), chunk_size):
        chunk = pending[start : start + chunk_size]
        commit(check_group(chunk, lean_project, args.timeout, args.repair_simple))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
