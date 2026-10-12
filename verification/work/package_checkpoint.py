"""Bundle final proof and reproducible checks, excluding unrelated research."""
from pathlib import Path
import shutil, json, hashlib, zipfile
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'output'; OUT.mkdir(exist_ok=True)
stage=OUT/'q_zeta3_checkpoint_2026-10-11'; stage.mkdir(exist_ok=True)
name='q_zeta3_proof_candidate_2026-10-11'
for suffix in ['.tex','.pdf']:
    shutil.copy2(OUT/(name+suffix),stage/(name+suffix))
shutil.copy2(ROOT/'work/README_checkpoint.txt',stage/'README.txt')
files=['source/zeta7-port/qhankel.py','work/normality.md','work/verify_assembly.py','work/assembly_verification.json','work/package_checkpoint.py','work/README_checkpoint.txt']
for sub in ['analytic','valuation','audit','denominators','denominator_repair','denominator_independent','fresh_audit','fresh_arithmetic']:
    files += [str(f.relative_to(ROOT)) for f in (ROOT/'work'/sub).glob('*') if f.is_file() and f.suffix in ['.py','.md','.json','.jsonl']]
for rel in sorted(set(files)):
    dst=stage/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/rel,dst)
record=json.loads((ROOT/'work/assembly_verification.json').read_text())
record.update({
    'date':'2026-10-11',
    'claim':'For every integer p>=2, sum_{n>=1} n^2/(p^n-1) is irrational.',
    'status':'Complete internally audited proof candidate; not formally verified or externally reviewed.',
    'independent_arithmetic_determinants':100,
    'larger_interval_certificate':json.loads((ROOT/'work/audit/fast_K60.json').read_text()),
    'proof_inputs':[
        'work/analytic/ANALYTIC_BOUND.md','work/valuation/PROOF.md','work/normality.md',
        'work/denominator_independent/PROOF.md','work/denominators/PROOF.md'],
    'internal_audits':[
        'work/fresh_audit/ANALYTIC_NORMALITY.md','work/fresh_arithmetic/AUDIT.md',
        'work/fresh_arithmetic/ASSEMBLY_AUDIT.md'],
    'source_urls':['https://arxiv.org/abs/0712.1762','https://doi.org/10.1007/s40993-016-0042-x'],
})
record['sha256']={str(f.relative_to(stage)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(stage.rglob('*')) if f.is_file()}
(stage/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
shutil.copy2(stage/'verification.json',OUT/'q_zeta3_verification_2026-10-11.json')
archive=OUT/'q_zeta3_checkpoint_2026-10-11.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for f in sorted(stage.rglob('*')):
        if f.is_file():z.write(f,f.relative_to(stage))
print(json.dumps({'archive':str(archive),'files':len(list(stage.rglob('*'))),'bytes':archive.stat().st_size}))
