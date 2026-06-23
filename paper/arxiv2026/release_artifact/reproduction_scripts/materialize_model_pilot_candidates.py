"""Convert model pilot outputs into Lean-checkable candidate files.

Input rows should contain at least `prompt_id` and `prediction`. The script
joins them with a pilot `targets.jsonl` file, extracts task-specific candidate
payloads, and writes JSONL files accepted by `check_lean_candidate.py`.
"""

from __future__ import annotations

import argparse
import json
import re
import textwrap
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
THEOREM_PATTERN = re.compile(r"\btheorem\s+[A-Za-z_][A-Za-z0-9_'.]*")
UNICODE_REPLACEMENTS = {
    "ℝ": "Real",
    "ℕ": "Nat",
    "→": "->",
    "λ": "lambda",
}
PROSE_PREFIXES = (
    "here is",
    "here's",
    "the proof",
    "proof:",
    "explanation:",
    "note:",
)
BLOCK_OPENING_PREFIXES = ("constructor", "case ", "| ", "·", "suffices ")


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    if not path.is_file():
        raise ValueError(f"file not found: {path}")
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        item = json.loads(line)
        if not isinstance(item, dict):
            raise ValueError(f"{path}:{line_number}: expected JSON object")
        rows.append(item)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def require_string(data: dict[str, Any], key: str, context: str) -> str:
    value = data.get(key)
    if not isinstance(value, str):
        raise ValueError(f"{context}: missing string field {key!r}")
    return value


def strip_code_fence(text: str) -> str:
    stripped = text.strip()
    if "```" not in stripped:
        if stripped.startswith("`") and stripped.endswith("`") and stripped.count("`") == 2:
            return stripped[1:-1].strip()
        return stripped
    blocks = re.findall(r"```(?:[A-Za-z0-9_+-]+)?\s*(.*?)```", stripped, flags=re.DOTALL)
    if blocks:
        return blocks[0].strip()
    return "\n".join(line for line in stripped.splitlines() if not line.strip().startswith("```")).strip()


def normalize_lean_text(text: str) -> str:
    for source, target in UNICODE_REPLACEMENTS.items():
        text = text.replace(source, target)
    return text


def leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def strip_accidental_nested_indent(lines: list[str]) -> list[str]:
    if len(lines) < 2 or leading_spaces(lines[0]) != 0:
        return lines
    first = lines[0].strip()
    if first.endswith("=>") or first.endswith(":= by") or first.startswith(BLOCK_OPENING_PREFIXES):
        return lines
    if first.startswith("have ") and ":=" not in first:
        return lines
    nonempty_tail = [line for line in lines[1:] if line.strip()]
    if not nonempty_tail:
        return lines
    min_indent = min(leading_spaces(line) for line in nonempty_tail)
    if min_indent < 2:
        return lines
    second = nonempty_tail[0].strip()
    if not (
        second == "calc"
        or second.startswith(
            (
                "apply ",
                "calc",
                "exact ",
                "have ",
                "intro ",
                "rcases ",
                "rw ",
                "simp",
                "unfold ",
            )
        )
    ):
        return lines
    return [lines[0], *[line[min_indent:] if leading_spaces(line) >= min_indent else line for line in lines[1:]]]


def extract_statement(prediction: str) -> str | None:
    text = normalize_lean_text(strip_code_fence(prediction))
    match = THEOREM_PATTERN.search(text)
    if not match:
        return None
    statement = text[match.start() :].strip()
    if ":= by" in statement:
        statement = statement.split(":= by", 1)[0].strip()
    elif ":=" in statement:
        statement = statement.split(":=", 1)[0].strip()
    lines = []
    for line in statement.splitlines():
        stripped = line.strip()
        if not stripped:
            if lines:
                break
            continue
        lower = stripped.lower()
        if lines and (lower.startswith("proof") or lower.startswith("explanation") or lower.startswith("note")):
            break
        lines.append(stripped)
    statement = " ".join(lines).strip()
    if statement.endswith(":"):
        statement = statement[:-1].rstrip()
    return statement or None


def extract_proof(prediction: str) -> str | None:
    text = normalize_lean_text(strip_code_fence(prediction))
    text = text.strip()
    if text.startswith("`"):
        text = text[1:].lstrip()
    if text.endswith("`"):
        text = text[:-1].rstrip()
    if ":= by" in text and THEOREM_PATTERN.search(text):
        text = text.split(":= by", 1)[1]
    elif text.lstrip().startswith(":= by"):
        text = text.split(":= by", 1)[1]
    raw_lines = [line.rstrip() for line in textwrap.dedent(text.strip("\n")).splitlines()]
    preserve_indentation = any(
        line.strip() == "calc" or line.strip().startswith("calc ") or line.strip().endswith(":= by")
        for line in raw_lines
    )
    lines = []
    for line in raw_lines:
        stripped = line.strip()
        lower = stripped.lower()
        if not stripped or stripped.startswith("--"):
            continue
        if any(lower.startswith(prefix) for prefix in PROSE_PREFIXES):
            continue
        if stripped.endswith(","):
            stripped = stripped[:-1].rstrip()
            line = line[: line.rfind(",")]
        lines.append(line.rstrip() if preserve_indentation else stripped)
    while lines and not lines[0].strip():
        lines.pop(0)
    if lines and lines[0].strip() == "by":
        lines.pop(0)
    lines = strip_accidental_nested_indent(lines)
    if not any(line.strip() and not line.strip().startswith("--") for line in lines):
        return None
    proof = "\n".join(lines).strip()
    return proof or None


def default_candidate_id(row: dict[str, Any], target: dict[str, Any]) -> str:
    model = row.get("model") or row.get("model_id") or "model"
    sample = row.get("sample_id") or row.get("sample") or "sample_0"
    safe_model = re.sub(r"[^A-Za-z0-9_]+", "_", str(model)).strip("_") or "model"
    safe_sample = re.sub(r"[^A-Za-z0-9_]+", "_", str(sample)).strip("_") or "sample_0"
    safe_record = re.sub(r"[^A-Za-z0-9_]+", "_", target["record_id"])
    return f"{safe_model}:{safe_record}:{target['task']}:{safe_sample}"


def materialize(
    model_outputs: list[dict[str, Any]],
    targets_by_prompt: dict[str, dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    statement_candidates = []
    proof_candidates = []
    rejected = []

    for index, row in enumerate(model_outputs):
        context = f"model output {index}"
        try:
            prompt_id = require_string(row, "prompt_id", context)
            prediction = require_string(row, "prediction", context)
        except ValueError as exc:
            rejected.append({"row_index": index, "reason": "invalid_row", "detail": str(exc), "row": row})
            continue
        target = targets_by_prompt.get(prompt_id)
        if target is None:
            rejected.append({"row_index": index, "prompt_id": prompt_id, "reason": "unknown_prompt_id", "row": row})
            continue
        if row.get("error"):
            rejected.append(
                {
                    "row_index": index,
                    "prompt_id": prompt_id,
                    "record_id": target["record_id"],
                    "task": target["task"],
                    "reason": "api_error",
                    "status": row.get("status"),
                    "error": row.get("error"),
                }
            )
            continue
        task = target["task"]
        candidate_id = row.get("candidate_id") or default_candidate_id(row, target)
        base = {
            "schema_version": "0.1.0",
            "pilot_id": target["pilot_id"],
            "prompt_id": prompt_id,
            "record_id": target["record_id"],
            "candidate_id": candidate_id,
            "model": row.get("model") or row.get("model_id"),
        }
        if task == "statement_translation":
            statement = extract_statement(prediction)
            if statement is None:
                rejected.append(
                    {
                        "row_index": index,
                        "prompt_id": prompt_id,
                        "record_id": target["record_id"],
                        "task": task,
                        "reason": "no_theorem_statement",
                        "prediction": prediction,
                    }
                )
                continue
            statement_candidates.append({**base, "statement": statement, "proof": "sorry"})
        elif task == "proof_completion":
            proof = extract_proof(prediction)
            if proof is None:
                rejected.append(
                    {
                        "row_index": index,
                        "prompt_id": prompt_id,
                        "record_id": target["record_id"],
                        "task": task,
                        "reason": "empty_proof_body",
                        "prediction": prediction,
                    }
                )
                continue
            proof_candidates.append({**base, "proof": proof})
        else:
            rejected.append(
                {
                    "row_index": index,
                    "prompt_id": prompt_id,
                    "record_id": target["record_id"],
                    "task": task,
                    "reason": "unsupported_task",
                    "prediction": prediction,
                }
            )

    return statement_candidates, proof_candidates, rejected


def summary(
    statement_candidates: list[dict[str, Any]],
    proof_candidates: list[dict[str, Any]],
    rejected: list[dict[str, Any]],
    output_dir: Path,
) -> dict[str, Any]:
    task_counts = Counter({"statement_translation": len(statement_candidates), "proof_completion": len(proof_candidates)})
    rejection_counts = Counter(str(row["reason"]) for row in rejected)
    return {
        "schema_version": "0.1.0",
        "report_kind": "model_pilot_candidate_materialization",
        "output_dir": str(output_dir.relative_to(ROOT)),
        "candidate_counts": dict(task_counts),
        "rejected_outputs": len(rejected),
        "rejections_by_reason": dict(sorted(rejection_counts.items())),
        "files": {
            "statement_candidates": str((output_dir / "statement_candidates.jsonl").relative_to(ROOT)),
            "proof_candidates": str((output_dir / "proof_candidates.jsonl").relative_to(ROOT)),
            "rejected_outputs": str((output_dir / "rejected_outputs.jsonl").relative_to(ROOT)),
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("model_outputs", type=Path, help="JSONL rows with prompt_id and prediction")
    parser.add_argument("--targets", type=Path, required=True, help="targets.jsonl from prepare_model_pilot.py")
    parser.add_argument("--output-dir", type=Path, help="candidate output directory")
    parser.add_argument("--fail-on-rejects", action="store_true", help="return nonzero if any output row is rejected")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    model_outputs = load_jsonl(args.model_outputs)
    target_rows = load_jsonl(args.targets)
    targets_by_prompt = {require_string(row, "prompt_id", "target row"): row for row in target_rows}

    output_dir = args.output_dir or (args.model_outputs.resolve().parent / "candidates")
    output_dir.mkdir(parents=True, exist_ok=True)

    statement_candidates, proof_candidates, rejected = materialize(model_outputs, targets_by_prompt)
    write_jsonl(output_dir / "statement_candidates.jsonl", statement_candidates)
    write_jsonl(output_dir / "proof_candidates.jsonl", proof_candidates)
    write_jsonl(output_dir / "rejected_outputs.jsonl", rejected)
    payload = summary(statement_candidates, proof_candidates, rejected, output_dir.resolve())
    (output_dir / "materialize_summary.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 1 if args.fail_on_rejects and rejected else 0


if __name__ == "__main__":
    raise SystemExit(main())
