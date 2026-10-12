#!/usr/bin/env bash
# Build the production library and check its transitive axiom dependencies.
# The separate Challenge statement template is not a solution dependency.
set -euo pipefail
cd "$(dirname "$0")/.."

# Use the source inventory and shared checker when running in the full repository.
if [[ -f ../scripts/check_axioms.py && -f ../scripts/formal_status.py && -f ../Makefile ]]; then
  exec make -C .. formal-proof
fi

# The standalone Lean bundle has no parent Makefile or Python helpers. Build and
# enforce the same complete transitive axiom gate directly from its audit module.
lake build QZeta3 QZeta3Audit.Solution
lake env lean QZeta3/Meta/AxiomsAudit.lean > audit-axioms.log
python3 - <<'PY'
from collections import Counter
from pathlib import Path
import re

source = Path("QZeta3/Meta/AxiomsAudit.lean").read_text()
text = Path("audit-axioms.log").read_text()
expected = re.findall(r"^#print axioms (\S+)\s*$", source, re.MULTILINE)
required = {"QZeta3.theorem11", "QZeta3Challenge.irrational_qzeta3",
            "QZeta3.irrational_xi_elementary", "QZeta3.irrational_qzeta3_elementary"}

def require(condition, message):
    if not condition:
        raise SystemExit(f"Axiom audit failed: {message}")

require(required <= set(expected) and len(expected) == len(set(expected)),
        "Audit source omits a public theorem or repeats a declaration")
require("sorryAx" not in text, "Placeholder dependency present")
require(not re.search(r"\berror\s*:", text, re.IGNORECASE), "Lean audit contains an error")
rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
counts = Counter(name for name, _ in rows)
missing = set(expected) - counts.keys()
unexpected = counts.keys() - set(expected)
repeated = {name for name, count in counts.items() if count != 1}
require(not (missing or unexpected or repeated),
        f"missing={sorted(missing)}, unexpected={sorted(unexpected)}, repeated={sorted(repeated)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, names in rows:
    axioms = {item.strip() for item in names.split(",") if item.strip()}
    require(axioms <= allowed, f"{name}: unapproved dependencies {sorted(axioms - allowed)}")
print(f"Axiom allowlist passed for all {len(rows)} expected declarations in the supplied fresh log.")
PY
lake env lean QZeta3/Meta/SecondProofAudit.lean > second-proof-dependencies.log
