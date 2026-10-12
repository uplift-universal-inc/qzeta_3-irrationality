"""Require a complete fresh Lean axiom report with only standard dependencies."""

import argparse
from collections import Counter
from pathlib import Path
import re


def check_report(text: str, audit_source: str) -> int:
    """Check every declaration requested by the checked-in audit module."""
    expected = re.findall(r"^#print axioms (\S+)\s*$", audit_source, re.MULTILINE)
    required = {"QZeta3.theorem11", "QZeta3Challenge.irrational_qzeta3",
                "QZeta3.irrational_xi_elementary", "QZeta3.irrational_qzeta3_elementary"}
    if not required <= set(expected) or len(expected) != len(set(expected)):
        raise ValueError("Audit source omits a public theorem or repeats a declaration")
    if "sorryAx" in text:
        raise ValueError("Placeholder dependency present")
    if re.search(r"\berror\s*:", text, re.IGNORECASE):
        raise ValueError("Lean audit contains an error")

    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    counts = Counter(name for name, _ in rows)
    missing = set(expected) - counts.keys()
    unexpected = counts.keys() - set(expected)
    repeated = {name for name, count in counts.items() if count != 1}
    if missing or unexpected or repeated:
        raise ValueError(
            f"Incomplete or inconsistent audit: missing={sorted(missing)}, "
            f"unexpected={sorted(unexpected)}, repeated={sorted(repeated)}"
        )
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, names in rows:
        axioms = {item.strip() for item in names.split(",") if item.strip()}
        if not axioms <= allowed:
            raise ValueError(f"{name}: unapproved dependencies {sorted(axioms - allowed)}")
    return len(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument(
        "--audit-source", type=Path,
        default=Path(__file__).resolve().parents[1] / "lean/QZeta3/Meta/AxiomsAudit.lean",
    )
    args = parser.parse_args()
    try:
        count = check_report(args.log.read_text(), args.audit_source.read_text())
    except (OSError, ValueError) as error:
        parser.exit(1, f"Axiom audit failed: {error}\n")
    print(f"Axiom allowlist passed for all {count} expected declarations in the supplied fresh log.")


if __name__ == "__main__":
    main()
