#!/usr/bin/env python3
"""Resolve the Route A smoke build status from all available checkpoint files."""

from __future__ import annotations

import argparse
import json
import os
import shlex
from pathlib import Path


def read_status_file(path: Path) -> str:
    if not path.exists():
        return ""
    status = ""
    for raw_line in path.read_text(errors="ignore").splitlines():
        if raw_line.startswith("exit_code="):
            status = raw_line.split("=", 1)[1].strip()
    return status


def read_direct_json(path: Path) -> str:
    if not path.exists():
        return ""
    try:
        value = json.loads(path.read_text(errors="ignore")).get("exit_code", "")
    except Exception:
        return ""
    return str(value).strip()


def resolve_status() -> tuple[str, str]:
    status = os.environ.get("BUILD_EXIT_CODE", "").strip()
    source = "step_output"
    if not status:
        status = read_status_file(Path("route-a-build-status.txt"))
        source = "route-a-build-status.txt"
    if not status:
        status = read_direct_json(Path("route-a-direct-build-status.json"))
        source = "route-a-direct-build-status.json"
    if status == "running":
        # The build step was killed before final cleanup. Treat it as a
        # checkpointable termination rather than an opaque setup failure.
        return "143", f"{source}:running"
    return status, source


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--shell",
        action="store_true",
        help="Emit shell assignments for status/source.",
    )
    args = parser.parse_args()

    status, source = resolve_status()
    if args.shell:
        print(f"status={shlex.quote(status)}")
        print(f"source={shlex.quote(source)}")
    else:
        print(json.dumps({"status": status, "source": source}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
