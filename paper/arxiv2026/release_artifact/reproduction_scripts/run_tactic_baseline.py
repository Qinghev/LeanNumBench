"""Run deterministic Lean tactic baselines over LeanNumBench proof-completion rows.

This baseline does not call an LLM and does not use target theorem names.  It
tries a small fixed portfolio of generic Lean tactic scripts against the frozen
LeanNumBench statements and records which rows are solved by tactics alone.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parents[0]
sys.path.insert(0, str(SCRIPT_DIR))

from check_lean_candidate import (  # noqa: E402
    DEFAULT_LEAN_PROJECT,
    load_records,
    module_from_file,
    namespace_lines,
    proof_candidate_name,
    rename_theorem,
    statement_translation_target,
)


ERROR_LINE_PATTERN = re.compile(r"Candidate\.lean:(\d+):\d+: error:")

BASELINE_PROOFS: dict[str, str] = {
    "rfl": "rfl",
    "simp": "simp",
    "simpa": "simpa",
    "simp_all": "simp_all",
    "norm_num": "norm_num",
    "ring": "ring",
    "ring_nf": "ring_nf",
    "linarith": "linarith",
    "nlinarith": "nlinarith",
    "omega": "omega",
    "aesop": "aesop",
    "simp_ring_nf": "simp\nring_nf",
    "simp_all_ring_nf": "simp_all\nring_nf",
}


def run_lean_source(source: str, lean_project: Path, timeout: int) -> dict[str, Any]:
    lean_project = lean_project.resolve()
    scratch_root = lean_project / ".nabench_tmp"
    scratch_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="tactic_baseline_", dir=scratch_root) as tmp_dir:
        candidate_path = Path(tmp_dir) / "Candidate.lean"
        candidate_path.write_text(source, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(candidate_path)],
            cwd=lean_project,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    return {
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "output": completed.stdout + completed.stderr,
    }


def build_source(records: list[dict[str, Any]], baseline_id: str, proof: str) -> tuple[str, list[dict[str, Any]]]:
    imports = sorted({module_from_file(record["formal"]["file"]) for record in records})
    lines = [
        *(f"import {module_name}" for module_name in imports),
        "",
        "set_option autoImplicit false",
        "set_option maxHeartbeats 200000",
        "open scoped BigOperators",
        "",
    ]
    spans: list[dict[str, Any]] = []
    for index, record in enumerate(records):
        item = {"record_id": record["id"], "candidate_id": baseline_id}
        name = proof_candidate_name(item, index)
        opens, closes = namespace_lines(record)
        theorem_lines = f"{rename_theorem(statement_translation_target(record), name)} := by".splitlines()
        start_line = len(lines) + 1
        lines.extend(
            [
                f"-- {baseline_id}: {record['id']}",
                *opens,
                "",
                *theorem_lines,
                *[f"  {line}" if line else "" for line in proof.strip().splitlines()],
                "",
                *closes,
                "",
            ]
        )
        end_line = len(lines)
        spans.append(
            {
                "record_id": record["id"],
                "category": record["category"],
                "difficulty": record["difficulty"],
                "baseline": baseline_id,
                "start_line": start_line,
                "end_line": end_line,
            }
        )
    return "\n".join(lines), spans


def line_to_record(line_number: int, spans: list[dict[str, Any]]) -> str | None:
    for span in spans:
        if span["start_line"] <= line_number <= span["end_line"]:
            return str(span["record_id"])
    preceding = [span for span in spans if span["start_line"] <= line_number]
    if preceding:
        return str(preceding[-1]["record_id"])
    return None


def failed_records_from_output(output: str, spans: list[dict[str, Any]]) -> set[str]:
    failed: set[str] = set()
    for match in ERROR_LINE_PATTERN.finditer(output):
        record_id = line_to_record(int(match.group(1)), spans)
        if record_id is not None:
            failed.add(record_id)
    return failed


def run_baseline(
    records: list[dict[str, Any]],
    baseline_id: str,
    proof: str,
    lean_project: Path,
    timeout: int,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    source, spans = build_source(records, baseline_id, proof)
    try:
        result = run_lean_source(source, lean_project, timeout)
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        result = {
            "returncode": None,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "output": (exc.stdout or "") + (exc.stderr or ""),
        }
        timed_out = True

    if result["returncode"] == 0:
        failed = set()
    else:
        failed = failed_records_from_output(str(result["output"]), spans)
        if timed_out and not failed:
            failed = {record["id"] for record in records}

    rows = []
    for record in records:
        passed = record["id"] not in failed and not timed_out
        rows.append(
            {
                "record_id": record["id"],
                "category": record["category"],
                "difficulty": record["difficulty"],
                "baseline": baseline_id,
                "passed": passed,
            }
        )

    summary = {
        "baseline": baseline_id,
        "proof": proof,
        "total": len(records),
        "passed": sum(1 for row in rows if row["passed"]),
        "failed": sum(1 for row in rows if not row["passed"]),
        "accuracy_pct": round(100.0 * sum(1 for row in rows if row["passed"]) / len(records), 1)
        if records
        else 0.0,
        "timed_out": timed_out,
        "returncode": result["returncode"],
    }
    return summary, rows


def summarize_best(records: list[dict[str, Any]], all_rows: list[dict[str, Any]]) -> dict[str, Any]:
    passed_by_record: dict[str, list[str]] = defaultdict(list)
    for row in all_rows:
        if row["passed"]:
            passed_by_record[row["record_id"]].append(row["baseline"])

    by_family: dict[str, Counter[str]] = defaultdict(Counter)
    by_difficulty: dict[str, Counter[str]] = defaultdict(Counter)
    record_rows = []
    for record in records:
        baselines = passed_by_record.get(record["id"], [])
        solved = bool(baselines)
        by_family[record["category"]]["total"] += 1
        by_family[record["category"]]["solved"] += int(solved)
        by_difficulty[str(record["difficulty"])]["total"] += 1
        by_difficulty[str(record["difficulty"])]["solved"] += int(solved)
        record_rows.append(
            {
                "record_id": record["id"],
                "category": record["category"],
                "difficulty": record["difficulty"],
                "solved_by_tactic_portfolio": solved,
                "passing_baselines": ";".join(baselines),
            }
        )

    solved_total = sum(1 for row in record_rows if row["solved_by_tactic_portfolio"])
    return {
        "total": len(records),
        "solved_by_tactic_portfolio": solved_total,
        "unsolved_by_tactic_portfolio": len(records) - solved_total,
        "accuracy_pct": round(100.0 * solved_total / len(records), 1) if records else 0.0,
        "by_family": {
            family: {
                "total": counts["total"],
                "solved": counts["solved"],
                "accuracy_pct": round(100.0 * counts["solved"] / counts["total"], 1)
                if counts["total"]
                else 0.0,
            }
            for family, counts in sorted(by_family.items())
        },
        "by_difficulty": {
            difficulty: {
                "total": counts["total"],
                "solved": counts["solved"],
                "accuracy_pct": round(100.0 * counts["solved"] / counts["total"], 1)
                if counts["total"]
                else 0.0,
            }
            for difficulty, counts in sorted(by_difficulty.items(), key=lambda item: int(item[0]))
        },
        "record_rows": record_rows,
    }


def write_csv(path: Path, rows: list[dict[str, Any]], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-project", type=Path, default=DEFAULT_LEAN_PROJECT)
    parser.add_argument("--timeout", type=int, default=240)
    parser.add_argument("--baselines", nargs="*", choices=sorted(BASELINE_PROOFS), default=sorted(BASELINE_PROOFS))
    parser.add_argument("--output-json", type=Path, default=ROOT / "data" / "baselines" / "tactic_baseline_160.json")
    parser.add_argument("--summary-csv", type=Path, default=ROOT / "data" / "baselines" / "tactic_baseline_160_by_baseline.csv")
    parser.add_argument("--rows-csv", type=Path, default=ROOT / "data" / "baselines" / "tactic_baseline_160_rows.csv")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    records = load_records()
    all_rows: list[dict[str, Any]] = []
    summaries = []
    for baseline_id in args.baselines:
        summary, rows = run_baseline(
            records,
            baseline_id,
            BASELINE_PROOFS[baseline_id],
            args.lean_project,
            args.timeout,
        )
        summaries.append(summary)
        all_rows.extend(rows)
        print(
            f"{baseline_id}: {summary['passed']}/{summary['total']} "
            f"({summary['accuracy_pct']}%)",
            flush=True,
        )

    best = summarize_best(records, all_rows)
    payload = {
        "schema_version": "0.1.0",
        "report_kind": "tactic_baseline",
        "dataset": "LeanNumBench",
        "records": len(records),
        "baselines": summaries,
        "portfolio": {key: value for key, value in best.items() if key != "record_rows"},
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(
        args.summary_csv,
        summaries,
        ["baseline", "proof", "total", "passed", "failed", "accuracy_pct", "timed_out", "returncode"],
    )
    write_csv(
        args.rows_csv,
        best["record_rows"],
        ["record_id", "category", "difficulty", "solved_by_tactic_portfolio", "passing_baselines"],
    )
    print(
        f"portfolio: {best['solved_by_tactic_portfolio']}/{best['total']} "
        f"({best['accuracy_pct']}%)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
