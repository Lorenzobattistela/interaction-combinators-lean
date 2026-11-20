#!/usr/bin/env python3
"""Extract Lean declarations, verbatim, into docs/paper/snip/.

Usage:  python3 docs/paper/extract.py      (reads docs/paper/snippets.txt, writes docs/paper/snip/)

Each line of docs/paper/snippets.txt is

    id | path/to/File.lean | Declaration.name | mode

A mode that ends in `-` (`stmt-`, `full-`) drops the docstring, the field docstrings and the
comment-only lines: what is left is still a slice of the source lines, with lines removed.

mode is `stmt` (docstring + statement, cut before the `:=`, `where` or first `|` alternative
that ends the statement) or `full` (docstring + whole declaration, up to the next blank line).
Several names separated by commas are concatenated, with a blank line between them.
A name may end in `#2` to pick the second match in the file, and in `@full` or `@stmt` to
override the mode of the line for that name.

The name is matched as written, then with leading namespace components dropped, because a file
that opens `namespace Translation` declares `NetTr.equiv`, not `Translation.NetTr.equiv`.
Nothing is retyped: the output is a slice of the source lines. A declaration that is not found
is reported and the script exits with status 1.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DOCS = os.path.join(ROOT, "docs", "paper")
KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)"
MOD = r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+|@\[[^\]]*\]\s*)*"
OPEN, CLOSE = "([{⟨", ")]}⟩"


def find(lines, name):
    """Index of the line that declares `name`, trying shorter and shorter suffixes."""
    nth = 1
    if "#" in name:
        name, k = name.split("#")
        nth = int(k)
    parts = name.split(".")
    for i in range(len(parts)):
        cand = ".".join(parts[i:])
        # First the name exactly as declared, then under any prefix (`_root_.INet.` ...).
        for prefix in ("", r"(?:[\w']+\.)+"):
            rx = re.compile(r"^\s*" + MOD + KW + r"\s+" + prefix + re.escape(cand)
                            + r"(?![\w.'!?₀-₉])")
            hits = [j for j, l in enumerate(lines) if rx.match(l)]
            if len(hits) >= nth:
                return hits[nth - 1], len(hits)
    return None, 0


def doc_start(lines, j):
    """Go up from the declaration to the start of its docstring and attributes."""
    k = j
    while k > 0 and lines[k - 1].strip().startswith("@["):
        k -= 1
    if k > 0 and lines[k - 1].rstrip().endswith("-/"):
        m = k - 1
        while m >= 0 and "/--" not in lines[m]:
            if "/-!" in lines[m] or (lines[m].strip() == "" and m < k - 1 and False):
                return k
            m -= 1
        if m >= 0:
            return m
    return k


def stmt_end(lines, j):
    """Lines j.. up to the end of the statement; returns the list of output lines."""
    depth = 0
    out = []
    for k in range(j, len(lines)):
        line = lines[k]
        if k > j and line.strip() == "":
            return out
        if k > j and depth == 0 and line.lstrip().startswith("| "):
            return out
        i = 0
        while i < len(line):
            c = line[i]
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth -= 1
            elif depth == 0 and line.startswith(":=", i):
                head = line[:i].rstrip()
                if head:
                    out.append((k, head))
                return out
            elif depth == 0 and line.startswith("--", i):
                break
            i += 1
        if depth == 0 and re.search(r"\swhere\s*$", line):
            out.append((k, line.rstrip()))
            return out
        out.append((k, line.rstrip()))
    return out


def full_end(lines, j):
    out = []
    for k in range(j, len(lines)):
        if k > j and lines[k].strip() == "":
            break
        out.append((k, lines[k].rstrip()))
    return out


def strip_comments(body):
    """Drop `--` comment lines and `/-- ... -/` docstrings from a list of (index, line)."""
    out, indoc = [], False
    for k, t in body:
        st = t.strip()
        if indoc:
            if "-/" in st:
                indoc = False
            continue
        if st.startswith("/--"):
            if "-/" not in st:
                indoc = True
            continue
        if st.startswith("--"):
            continue
        out.append((k, t))
    return out


def extract(path, name, mode):
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        lines = f.read().split("\n")
    j, n = find(lines, name)
    if j is None:
        return None, 0
    bare = mode.endswith("-")
    mode = mode.rstrip("-")
    s = doc_start(lines, j)
    head = [(k, lines[k].rstrip()) for k in range(s, j)]
    body = stmt_end(lines, j) if mode == "stmt" else full_end(lines, j)
    if bare:
        return strip_comments(body), n
    return head + body, n


def main():
    missing, ambiguous, count = [], [], 0
    os.makedirs(os.path.join(DOCS, "snip"), exist_ok=True)
    with open(os.path.join(DOCS, "snippets.txt"), encoding="utf-8") as f:
        for raw in f:
            raw = raw.strip()
            if not raw or raw.startswith("#"):
                continue
            sid, path, names, mode = [x.strip() for x in raw.split("|")]
            if not os.path.exists(os.path.join(ROOT, path)):
                missing.append((sid, path, "FILE"))
                continue
            chunks = []
            seen = set()  # source lines already quoted in this snippet
            for name in names.split(","):
                name = name.strip()
                m = mode
                if "@" in name:  # per-name mode: `plugTarget@full`
                    name, m = name.split("@")
                text, n = extract(path, name, m)
                if text is None:
                    missing.append((sid, path, name))
                    continue
                if n > 1 and "#" not in name:
                    ambiguous.append((sid, path, name, n))
                # Declarations written one after the other with no blank line come out as one
                # block: do not quote a line twice.
                text = [(k, t) for k, t in text if k not in seen]
                seen.update(k for k, _ in text)
                if text:
                    chunks.append("\n".join(t for _, t in text))
            with open(os.path.join(DOCS, "snip", sid + ".lean"), "w", encoding="utf-8") as g:
                g.write("\n\n".join(chunks) + "\n")
            count += 1
    print(f"{count} snippets written")
    for a in ambiguous:
        print("AMBIGUOUS (first match taken):", a)
    for m in missing:
        print("MISSING:", m)
    sys.exit(1 if missing else 0)


if __name__ == "__main__":
    main()
