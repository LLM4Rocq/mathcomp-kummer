#!/usr/bin/env python3
"""Automatically add \\rocqok and \\proves to blueprint .tex files.

This script reads the Rocq source files to determine which declarations
are proven (end with Qed./Defined. rather than Admitted.), then patches
the blueprint LaTeX sources so that:

  - Every proven statement gets \\rocqok (green border in the graph).
  - Every proof block inside a proven lemma gets \\proves{label} + \\rocqok
    (green fill in the graph).
  - Lemmas without a \\begin{proof} block that are proven get one added.

Run this before `rocqblueprint web` to keep the graph in sync with the code.

Usage:
    python3 blueprint/update_status.py
    cd blueprint/src && rocqblueprint web
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEORIES = ROOT / "theories"
BLUEPRINT_SRC = ROOT / "blueprint" / "src"


def parse_rocq_status(vfile: Path) -> dict[str, bool]:
    """Parse a .v file and return {decl_name: is_proven} for each declaration."""
    text = vfile.read_text()
    results = {}

    # Match Lemma/Theorem/Definition declarations and their terminators
    # We look for: (Lemma|Theorem|Definition|Corollary) name ... . ... (Qed|Defined|Admitted).
    decl_pattern = re.compile(
        r'\b(Lemma|Theorem|Definition|Corollary)\s+'
        r'(\w+)\b'
    )
    # Find all declaration positions
    decls = list(decl_pattern.finditer(text))

    for i, m in enumerate(decls):
        name = m.group(2)
        kind = m.group(1)
        start = m.start()
        # Region extends to next declaration or end of file
        end = decls[i + 1].start() if i + 1 < len(decls) else len(text)
        region = text[start:end]

        if kind == "Definition":
            # Definitions are always "proven" (they're just definitions)
            results[name] = True
        elif "Admitted." in region:
            results[name] = False
        elif "Qed." in region or "Defined." in region:
            results[name] = True
        else:
            results[name] = False

    return results


def build_status_map() -> dict[str, bool]:
    """Build a map from fully-qualified Rocq name to proven status."""
    status = {}
    for vfile in sorted(THEORIES.glob("*.v")):
        module = vfile.stem  # e.g. "divn_carry"
        for name, proven in parse_rocq_status(vfile).items():
            fqn = f"MathCompKummer.{module}.{name}"
            status[fqn] = proven
    return status


def update_tex_file(texfile: Path, status: dict[str, bool]) -> bool:
    """Update a single .tex file with \\rocqok and \\proves annotations.

    Returns True if the file was modified.
    """
    text = texfile.read_text()
    original = text

    # Step 1: Remove existing \rocqok and \proves lines (we'll re-add correct ones)
    text = re.sub(r'\n\s*\\rocqok\b[^\n]*', '', text)
    text = re.sub(r'\n\s*\\proves\{[^}]*\}[^\n]*', '', text)

    # Step 2: Find all \rocq{...} declarations and their labels
    # Pattern: within a begin{lemma/theorem/definition} block,
    # find \label{...} and \rocq{...}
    lines = text.split('\n')
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        new_lines.append(line)

        # Detect \rocq{MathCompKummer....} lines
        rocq_match = re.match(r'^(\s*)\\rocq\{(MathCompKummer\.\S+)\}\s*$', line)
        if rocq_match:
            indent = rocq_match.group(1)
            fqn = rocq_match.group(2)
            if status.get(fqn, False):
                new_lines.append(f"{indent}\\rocqok")
            i += 1
            continue

        # Detect \begin{proof} lines — add \proves and \rocqok
        proof_match = re.match(r'^(\s*)\\begin\{proof\}\s*$', line)
        if proof_match:
            indent = proof_match.group(1)
            # Walk backwards to find the label of the enclosing environment
            label = find_enclosing_label(lines, i)
            fqn = find_enclosing_rocq(lines, i)
            if label and fqn and status.get(fqn, False):
                new_lines.append(f"{indent}  \\proves{{{label}}}")
                new_lines.append(f"{indent}  \\rocqok")
            i += 1
            continue

        i += 1

    text = '\n'.join(new_lines)

    # Step 3: For proven declarations without a proof block, add one
    text = add_missing_proof_blocks(text, status)

    if text != original:
        texfile.write_text(text)
        return True
    return False


def find_enclosing_label(lines: list[str], proof_line: int) -> str | None:
    """Walk backwards from a \\begin{proof} to find the \\label{...}."""
    for j in range(proof_line - 1, max(proof_line - 20, -1), -1):
        m = re.search(r'\\label\{([^}]+)\}', lines[j])
        if m:
            return m.group(1)
        # Stop if we hit another \end or \begin of a theorem env
        if re.match(r'\s*\\end\{', lines[j]):
            break
    return None


def find_enclosing_rocq(lines: list[str], proof_line: int) -> str | None:
    """Walk backwards from a \\begin{proof} to find the \\rocq{...}."""
    for j in range(proof_line - 1, max(proof_line - 20, -1), -1):
        m = re.search(r'\\rocq\{(\S+)\}', lines[j])
        if m:
            return m.group(1)
        if re.match(r'\s*\\end\{', lines[j]):
            break
    return None


def add_missing_proof_blocks(text: str, status: dict[str, bool]) -> str:
    """For proven lemmas/theorems without a \\begin{proof}, add one before \\end{lemma}."""
    env_types = ['lemma', 'theorem']
    for env in env_types:
        # Find environments that have \rocq{} but no \begin{proof}
        pattern = re.compile(
            r'(\\begin\{' + env + r'\}.*?)(\\end\{' + env + r'\})',
            re.DOTALL
        )
        def add_proof(m):
            body = m.group(1)
            end = m.group(2)
            # Check if there's already a proof
            if r'\begin{proof}' in body:
                return m.group(0)
            # Find the \rocq and \label
            rocq_m = re.search(r'\\rocq\{(\S+)\}', body)
            label_m = re.search(r'\\label\{([^}]+)\}', body)
            if rocq_m and label_m:
                fqn = rocq_m.group(1)
                label = label_m.group(1)
                if status.get(fqn, False):
                    # Detect indentation from \end line
                    indent = re.match(r'(\s*)', end).group(1)
                    proof_block = (
                        f"{indent}  \\begin{{proof}}\n"
                        f"{indent}    \\proves{{{label}}}\n"
                        f"{indent}    \\rocqok\n"
                        f"{indent}  \\end{{proof}}\n"
                    )
                    return body + proof_block + end
            return m.group(0)

        text = pattern.sub(add_proof, text)
    return text


def main():
    # Build status from Rocq sources
    status = build_status_map()

    proven = [k for k, v in status.items() if v]
    admitted = [k for k, v in status.items() if not v]
    print(f"Rocq status: {len(proven)} proven, {len(admitted)} admitted")
    if admitted:
        for a in admitted:
            print(f"  Admitted: {a}")

    # Update each .tex file
    tex_files = [
        "ch_carry.tex",
        "ch_legendre.tex",
        "ch_kummer.tex",
        "ch_corollaries.tex",
        "ch_digits.tex",
    ]

    modified = 0
    for name in tex_files:
        path = BLUEPRINT_SRC / name
        if not path.exists():
            print(f"  Warning: {name} not found, skipping")
            continue
        if update_tex_file(path, status):
            print(f"  Updated: {name}")
            modified += 1
        else:
            print(f"  No changes: {name}")

    print(f"\nDone. {modified} file(s) updated.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
