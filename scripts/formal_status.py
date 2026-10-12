"""Static Lean obligation inventory; not a substitute for a kernel axiom audit."""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def code_only(text):
    """Mask nested comments and strings while preserving line numbers."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        c = text[i]
        pair = text[i:i+2]
        if depth:
            if pair == "/-":
                depth += 1; out.extend("  "); i += 2; continue
            if pair == "-/":
                depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if string:
            if c == "\\" and i+1 < len(text):
                out.extend("  "); i += 2; continue
            if c == '"': string = False
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if pair == "/-":
            depth = 1; out.extend("  "); i += 2; continue
        if pair == "--":
            j = text.find("\n", i)
            if j == -1: j = len(text)
            out.extend(" " * (j-i)); i = j; continue
        if c == '"': string = True; out.append(" ")
        else: out.append(c)
        i += 1
    return "".join(out)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--strict", action="store_true", help="Fail if source placeholders or custom axioms remain")
args = parser.parse_args()
findings = []
for path in sorted((ROOT / "lean/QZeta3").rglob("*.lean")):
    for n, line in enumerate(code_only(path.read_text()).splitlines(), 1):
        for match in re.finditer(r"\b(sorry|admit|sorryAx|axiom)\b", line):
            findings.append({"path": str(path.relative_to(ROOT)), "line": n, "token": match.group()})
out = {"kind": "static_source_inventory", "production_scope": "lean/QZeta3/**/*.lean",
       "placeholder_count": sum(x["token"] in ("sorry", "admit", "sorryAx") for x in findings),
       "custom_axiom_count": sum(x["token"] == "axiom" for x in findings),
       "findings": findings,
       "formal_completeness": "incomplete" if findings else "requires fresh kernel dependency audit",
       "kernel_build_replayed": False,
       "note": "A source scan cannot certify theorem dependencies. Run the pinned Lean axiom audit after a successful build."}
(ROOT / "certificates/formal-status.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
if args.strict and findings:
    raise SystemExit(1)
