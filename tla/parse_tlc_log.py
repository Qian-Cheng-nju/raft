#!/usr/bin/env python3
"""
Parse a TLC log and emit warnings/errors plus per-state diffs.

By default this prints warnings/errors, the full final state, and only the diff
from the previous state. Use --all-diffs to print every state diff instead.
"""

import argparse
import re
from pathlib import Path
from typing import Dict, List, Tuple


STATE_RE = re.compile(r"^State\s+(\d+)")
ASSIGN_RE = re.compile(r"^\s*/\\\s*([^\s=]+)\s*=\s*(.*)$")


def parse_states(lines: List[str]) -> List[Tuple[str, List[str]]]:
    """Group lines by State N sections."""
    states: List[Tuple[str, List[str]]] = []
    current_id = None
    current_lines: List[str] = []

    for raw in lines:
        line = raw.rstrip("\n")
        m = STATE_RE.match(line)
        if m:
            if current_id is not None:
                states.append((current_id, current_lines))
            current_id = m.group(1)
            current_lines = []
            continue
        if current_id is not None:
            current_lines.append(line)
    if current_id is not None:
        states.append((current_id, current_lines))
    return states


def parse_assignments(lines: List[str]) -> Dict[str, str]:
    """Parse variable assignments inside a state block."""
    curr_terms: Dict[str, str] = {}
    current_var = None
    buffer: List[str] = []

    def flush_var(var_name: str, buf: List[str]) -> None:
        if var_name is None:
            return
        curr_terms[var_name] = "\n".join(buf).strip()

    for line in lines:
        m = ASSIGN_RE.match(line)
        if m:
            flush_var(current_var, buffer)
            current_var = m.group(1)
            buffer = [m.group(2)]
        else:
            if current_var is not None:
                buffer.append(line)
    flush_var(current_var, buffer)
    return curr_terms


def print_warnings_errors(lines: List[str]) -> None:
    print("Warnings/Errors:")
    for raw in lines:
        line = raw.rstrip("\n")
        lower = line.lower()
        if lower.startswith("warning") or lower.startswith("error"):
            print(line)
    print()


def print_state_diff(state_id: str, prev_terms: Dict[str, str], curr_terms: Dict[str, str]) -> None:
    added_keys = [k for k in curr_terms.keys() if k not in prev_terms]
    removed_keys = [k for k in prev_terms.keys() if k not in curr_terms]
    changed_keys = [
        k for k in curr_terms.keys()
        if k in prev_terms and curr_terms[k].strip() != prev_terms[k].strip()
    ]

    print(f"State {state_id}:")
    if not added_keys and not removed_keys and not changed_keys:
        print("  (no changes from previous state)")
    if added_keys:
        print("  Added:")
        for k in added_keys:
            print(f"    {k} = {curr_terms[k]}")
    if removed_keys:
        print("  Removed:")
        for k in removed_keys:
            print(f"    {k} = {prev_terms[k]}")
    if changed_keys:
        print("  Changed:")
        for k in changed_keys:
            prev_val = prev_terms[k].strip()
            curr_val = curr_terms[k].strip()
            if prev_val != "<<>>" and curr_val == "<<>>":
                print(f"    {k}: emptied to <<>>")
                continue
            print(f"    {k}:")
            print(f"      was: {prev_val}")
            print(f"      now: {curr_val}")
    print()


def print_all_state_diffs(states: List[Tuple[str, List[str]]]) -> None:
    prev_terms: Dict[str, str] = {}

    for state_id, lines in states:
        curr_terms = parse_assignments(lines)
        print_state_diff(state_id, prev_terms, curr_terms)
        prev_terms = curr_terms


def print_final_state(state_id: str, lines: List[str]) -> None:
    print(f"Final state {state_id}:")
    for line in lines:
        print(line)
    print()


def print_last_state_diff(states: List[Tuple[str, List[str]]]) -> None:
    if not states:
        return
    curr_state_id, curr_lines = states[-1]
    prev_terms = parse_assignments(states[-2][1]) if len(states) > 1 else {}
    curr_terms = parse_assignments(curr_lines)
    print("Final state diff (vs previous):")
    print_state_diff(curr_state_id, prev_terms, curr_terms)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Condense TLC log into warnings/errors and per-state diffs."
    )
    parser.add_argument("log_path", type=Path, help="Path to TLC log file")
    parser.add_argument(
        "--all-diffs",
        action="store_true",
        help="Print diffs for every state instead of only the final diff.",
    )
    args = parser.parse_args()

    try:
        lines = args.log_path.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        raise SystemExit(f"Log not found: {args.log_path}")

    # Truncate anything after the TLC footer summary (e.g., "<n> states generated").
    for i, ln in enumerate(lines):
        if re.match(r"^\d+\s+states generated", ln.strip()):
            lines = lines[:i]
            break

    print_warnings_errors(lines)
    states = parse_states(lines)
    if not states:
        print("No states found.")
    else:
        final_state_id, final_lines = states[-1]
        print_final_state(final_state_id, final_lines)
        if args.all_diffs:
            print("State diffs:")
            print_all_state_diffs(states)
        else:
            print_last_state_diff(states)


if __name__ == "__main__":
    main()
