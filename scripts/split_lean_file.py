#!/usr/bin/env python3
import argparse
import re
from pathlib import Path

SAFE_CUT_RE = re.compile(r'^\s*$|^\s*(lemma|theorem|def|@[^\n]*\b(lemma|theorem|def)\b|end\b)')
IMPORT_RE   = re.compile(r'^\s*import\b')
OPEN_RE     = re.compile(r'^\s*(open\b|open scoped\b|open namespace\b)')
OPTION_RE   = re.compile(r'^\s*set_option\b')
NAMESPACE_RE= re.compile(r'^\s*namespace\s+([A-Za-z0-9_.]+)\s*$')
END_RE      = re.compile(r'^\s*end\b')
COMMENT_RE  = re.compile(r'^\s*--')

def detect_prologue(lines):
    """Heuristically detect a 'prologue' to copy into each chunk:
    - leading imports
    - set_option lines
    - open/open scoped
    - (optionally) a single `namespace Foo.Bar` which we'll replicate per chunk if --namespace not set.
    Stops at the first non-prologue line.
    """
    prologue = []
    ns_line = None
    for i, ln in enumerate(lines):
        if IMPORT_RE.match(ln) or OPTION_RE.match(ln) or OPEN_RE.match(ln) or COMMENT_RE.match(ln):
            prologue.append(ln)
            continue
        m = NAMESPACE_RE.match(ln)
        if m and ns_line is None:
            ns_line = ln.rstrip('\n')
            prologue.append(ln)
            continue
        # otherwise stop
        return prologue, ns_line, i
    # file is only prologue
    return prologue, ns_line, len(lines)

def choose_cut(lines, start, target_end):
    """Choose a safe cut position <= target_end, backing up to nearest SAFE_CUT_RE if found."""
    end = min(target_end, len(lines))
    if start >= end:
        return end
    i = end
    while i > start and (end - i) < 2000:
        if SAFE_CUT_RE.match(lines[i-1]):
            return i
        i -= 1
    return end

def main():
    ap = argparse.ArgumentParser(description='Split a Lean file into multiple chunk files.')
    ap.add_argument('input', type=Path, help='Path to the Lean source file to split (e.g., Generated_000004_100000.lean)')
    ap.add_argument('outdir', type=Path, help='Output directory where chunks will be written')
    ap.add_argument('--lines-per-chunk', type=int, default=5000, help='Maximum lines per chunk (default: 5000)')
    ap.add_argument('--prefix', type=str, default='Chunk', help='Base prefix for chunk file names (default: Chunk)')
    ap.add_argument('--namespace', type=str, default=None, help='Optional namespace to wrap each chunk (e.g., Goldbach.FiniteBase)')
    ap.add_argument('--max-rec-depth', type=int, default=200000, help='set_option maxRecDepth value to inject per chunk')
    ap.add_argument('--max-heartbeats', type=int, default=200000000, help='set_option maxHeartbeats value to inject per chunk')
    ap.add_argument('--copy-prologue', action='store_true', help='Copy detected prologue (imports/open/set_option/namespace) into each chunk')
    ap.add_argument('--start-index', type=int, default=1, help='Chunk numbering starts at this index (default: 1)')
    ap.add_argument('--dry-run', action='store_true', help='Show planned cuts but do not write files')
    args = ap.parse_args()

    src = args.input.read_text(encoding='utf-8').splitlines(keepends=True)
    prologue, detected_ns_line, body_start = detect_prologue(src)
    body = src[body_start:]

    ns_to_use = args.namespace
    if ns_to_use is None:
        m = re.match(r'^\s*namespace\s+([A-Za-z0-9_.]+)\s*$', detected_ns_line or '')
        if m:
            ns_to_use = m.group(1)

    if ns_to_use:
        while body and END_RE.match(body[-1]):
            body.pop()

    chunks = []
    i = 0
    L = len(body)
    while i < L:
        target = i + args.lines_per_chunk
        cut = choose_cut(body, i, target)
        if cut <= i:
            cut = min(i + args.lines_per_chunk, L)
        chunks.append((i, cut))
        i = cut

    args.outdir.mkdir(parents=True, exist_ok=True)

    for idx, (a, b) in enumerate(chunks, start=args.start_index):
        out = args.outdir / f"{args.prefix}_{idx:02d}.lean"
        if args.dry_run:
            print(f"[dry-run] {out}  <-- lines {a+1+body_start} .. {b+body_start}")
            continue

        with out.open('w', encoding='utf-8') as f:
            f.write(f"set_option maxRecDepth {args.max_rec_depth}\n")
            f.write(f"set_option maxHeartbeats {args.max_heartbeats}\n\n")

            if args.copy_prologue:
                for ln in prologue:
                    if NAMESPACE_RE.match(ln):
                        continue
                    f.write(ln)
                f.write('\n')

            if ns_to_use:
                f.write(f"namespace {ns_to_use}\n\n")

            f.writelines(body[a:b])

            if b > a and not body[b-1].endswith('\n'):
                f.write('\n')

            if ns_to_use:
                f.write(f"\nend {ns_to_use}\n")

        print(f"Wrote {out}  (lines {a+1+body_start}..{b+body_start})")

if __name__ == '__main__':
    main()