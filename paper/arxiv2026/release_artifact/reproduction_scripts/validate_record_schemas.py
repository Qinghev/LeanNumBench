"""Validate LeanNumBench theorem records against the bundled JSON schema.

The validator intentionally uses only the Python standard library so the
artifact can be checked without installing extra packages. It implements the
JSON Schema keywords used by ``schemas/theorem-v0.1.schema.json``.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def type_matches(value: Any, expected: str) -> bool:
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if expected == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "null":
        return value is None
    raise ValueError(f"unsupported JSON schema type: {expected}")


def validate_value(value: Any, schema: dict[str, Any], path: str, issues: list[str]) -> None:
    if "const" in schema and value != schema["const"]:
        issues.append(f"{path}: expected const {schema['const']!r}, found {value!r}")
        return

    if "enum" in schema and value not in schema["enum"]:
        issues.append(f"{path}: value {value!r} not in enum {schema['enum']!r}")

    expected_type = schema.get("type")
    if expected_type is not None:
        expected_types = expected_type if isinstance(expected_type, list) else [expected_type]
        if not any(type_matches(value, item) for item in expected_types):
            issues.append(f"{path}: expected type {expected_type!r}, found {type(value).__name__}")
            return

    if isinstance(value, dict):
        required = schema.get("required", [])
        for key in required:
            if key not in value:
                issues.append(f"{path}: missing required property {key!r}")

        properties = schema.get("properties", {})
        if schema.get("additionalProperties") is False:
            for key in value:
                if key not in properties:
                    issues.append(f"{path}: unexpected property {key!r}")

        for key, subschema in properties.items():
            if key in value:
                validate_value(value[key], subschema, f"{path}.{key}", issues)

    if isinstance(value, list):
        min_items = schema.get("minItems")
        if min_items is not None and len(value) < min_items:
            issues.append(f"{path}: expected at least {min_items} items, found {len(value)}")
        item_schema = schema.get("items")
        if item_schema is not None:
            for index, item in enumerate(value):
                validate_value(item, item_schema, f"{path}[{index}]", issues)

    if isinstance(value, str):
        min_length = schema.get("minLength")
        if min_length is not None and len(value) < min_length:
            issues.append(f"{path}: expected string length >= {min_length}, found {len(value)}")
        pattern = schema.get("pattern")
        if pattern is not None and re.search(pattern, value) is None:
            issues.append(f"{path}: value {value!r} does not match pattern {pattern!r}")

    if isinstance(value, (int, float)) and not isinstance(value, bool):
        minimum = schema.get("minimum")
        maximum = schema.get("maximum")
        if minimum is not None and value < minimum:
            issues.append(f"{path}: expected >= {minimum}, found {value}")
        if maximum is not None and value > maximum:
            issues.append(f"{path}: expected <= {maximum}, found {value}")


def validate_records(root: Path = ROOT) -> dict[str, Any]:
    issues: list[str] = []
    schema_path = root / "schemas" / "theorem-v0.1.schema.json"
    index_path = root / "records" / "index.json"

    if not schema_path.is_file():
        return {"passed": False, "records": 0, "schema_errors": 1, "issues": [f"missing {schema_path}"]}
    if not index_path.is_file():
        return {"passed": False, "records": 0, "schema_errors": 1, "issues": [f"missing {index_path}"]}

    schema = load_json(schema_path)
    index = load_json(index_path)
    records = index.get("records", [])

    for item_number, item in enumerate(records, start=1):
        rel = item.get("path")
        if not isinstance(rel, str):
            issues.append(f"records/index.json[{item_number}]: missing string path")
            continue
        record_path = root / "records" / "theorems" / rel
        if not record_path.is_file():
            issues.append(f"{record_path.relative_to(root).as_posix()}: missing record file")
            continue
        record = load_json(record_path)
        validate_value(record, schema, record_path.relative_to(root).as_posix(), issues)

    return {
        "passed": not issues,
        "records": len(records),
        "schema_errors": len(issues),
        "issues": issues,
    }


def main() -> int:
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT
    payload = validate_records(root)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
