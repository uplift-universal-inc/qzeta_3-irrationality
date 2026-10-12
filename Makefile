.PHONY: paper check certificate examples formal-status formal-proof
paper:
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper paper/main.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper paper/main.tex
check:
	python3 verification/work/verify_assembly.py
	python3 verification/work/fresh_arithmetic/check.py
	python3 verification/work/denominator_repair/verify.py
	python3 scripts/write_examples.py
	python3 scripts/formal_status.py
certificate:
	python3 verification/work/audit/fast_verify.py 60
examples:
	python3 scripts/write_examples.py
formal-status:
	python3 scripts/formal_status.py
formal-proof:
	python3 scripts/formal_status.py --strict
	cd lean && lake build QZeta3 QZeta3Audit.Solution && lake env lean QZeta3/Meta/AxiomsAudit.lean > ../certificates/kernel-axioms.log
	python3 scripts/check_axioms.py certificates/kernel-axioms.log
	cd lean && lake env lean QZeta3/Meta/SecondProofAudit.lean > ../certificates/second-proof-dependencies.log
