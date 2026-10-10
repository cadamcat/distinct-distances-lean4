#!/usr/bin/env python3
"""Check that the proof's target matches Challenge.lean.

  check_target.py defs [FC_CHECKOUT]   definitions block of Challenge.lean equals that of
                                       DistinctDistances/Defs.lean and holds nothing besides the
                                       copied declarations; with FC_CHECKOUT, each declaration (with its
                                       docstring) appears verbatim in Formal Conjectures'
                                       FormalConjecturesForMathlib/Geometry/Metric.lean
  check_target.py types                builds DistinctDistances.Main; the elaborated statement of
                                       DistinctDistances.jsp_000900 and the definitions it uses, printed with pp.all,
                                       agree between Challenge.lean and DistinctDistances.Main; and the
                                       proof's axioms are within propext, Classical.choice, Quot.sound
  check_target.py statement            as `types`, without the axiom check (scripts/verify.sh checks the
                                       axioms separately and reports an open proof with its own exit status)
Exit 0 only when every check passes.
"""
import re, subprocess, sys, tempfile, os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BEGIN, END = '-- BEGIN FORMAL CONJECTURES DEFINITIONS', '-- END FORMAL CONJECTURES DEFINITIONS'
NAMES = ['DistinctDistances.jsp_000900', 'distanceSet', 'distinctDistances']
FC_METRIC = 'FormalConjecturesForMathlib/Geometry/Metric.lean'
FC_THEOREM = 'FormalConjectures/ErdosProblems/1083.lean'


def block(path):
    s = path.read_text()
    return s[s.index(BEGIN):s.index(END)]


PRE = '\nopen scoped Finset\n\nvariable {X : Type*} [MetricSpace X]\n'


def defs(fc):
    a, b = block(ROOT / 'Challenge.lean'), block(ROOT / 'DistinctDistances/Defs.lean')
    ok = a == b
    print(f'definitions block identical: {ok}')
    body = a[len(BEGIN):]
    framed = body.startswith(PRE)
    print(f'block opens with the Finset preamble and the variable line: {framed}')
    ok = ok and framed
    mid = body[len(PRE):] if framed else body
    has_dist = 'noncomputable def distanceSet' in mid
    has_num = 'noncomputable def distinctDistances' in mid
    print(f'block defines distanceSet: {has_dist}')
    print(f'block defines distinctDistances: {has_num}')
    ok = ok and has_dist and has_num
    extra = [kw for kw in ('\ntheorem ', '\nlemma ', '\naxiom ', '\ninstance ',
                           '\nstructure ', '\ninductive ', '\nclass ')
             if kw in mid]
    print(f'block holds no other declarations: {not extra}')
    ok = ok and not extra
    if fc:
        src = (Path(fc) / FC_METRIC).read_text()
        # each declaration with its docstring is one chunk; text between declarations would make a
        # chunk fail to match
        chunks = [c.strip() for c in re.split(r'\n(?=/--|noncomputable def)', mid)
                  if re.match(r'(/--|noncomputable def)', c.strip())]
        for c in chunks:
            hit = c in src
            print(f'verbatim in Formal Conjectures {FC_METRIC}: {hit}: {c.splitlines()[0][:70]}')
            ok = ok and hit
        ok = ok and len(chunks) >= 2
        thm_path = Path(fc) / FC_THEOREM
        if thm_path.exists():
            # The target intentionally strengthens Formal Conjectures' erdos_1083 (an n^(2/d - o(1))
            # lower bound) to the exact-order two-sided bound with n^(2/d); no textual match of the
            # theorem statement is expected. Record the upstream statement for the audit trail.
            thm = thm_path.read_text()
            m = re.search(r'theorem erdos_1083.*?(?::=|:= by|\n\s*:=)', thm, re.S)
            print(f'upstream {FC_THEOREM} present (statement match not required): {m is not None}')
        else:
            print(f'upstream {FC_THEOREM} not found under {fc}', file=sys.stderr)
            ok = False
    return ok


def printed(header_lines):
    body = header_lines + ['set_option pp.all true'] + \
        [f'#check @{NAMES[0]}'] + [f'#print {n}' for n in NAMES[1:]]
    fd, p = tempfile.mkstemp(prefix='.check_target_', suffix='.lean', dir=ROOT)
    with os.fdopen(fd, 'w') as f:
        f.write('\n'.join(body) + '\n')
    try:
        r = subprocess.run(['lake', 'env', 'lean', p], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(p)
    out = re.sub(r'^.*?:\d+:\d+: ', '', r.stdout, flags=re.M)
    return r.returncode, out


ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def axioms_of_main():
    fd, p = tempfile.mkstemp(prefix='.check_target_', suffix='.lean', dir=ROOT)
    with os.fdopen(fd, 'w') as f:
        f.write('import DistinctDistances.Main\n#print axioms DistinctDistances.jsp_000900\n')
    try:
        r = subprocess.run(['lake', 'env', 'lean', p], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(p)
    out = re.sub(r'\s+', ' ', r.stdout)
    if 'does not depend on any axioms' in out:
        return r.returncode, set()
    m = re.search(r'depends on axioms: \[(.*?)\]', out)
    return r.returncode, ({x.strip() for x in m.group(1).split(',')} if m else None)


def build_main():
    b0 = subprocess.run(['lake', 'build', 'DistinctDistances.Main'], cwd=ROOT, capture_output=True, text=True)
    print(f'lake build DistinctDistances.Main exit {b0.returncode}')
    if b0.returncode != 0:
        print((b0.stdout + b0.stderr)[-3000:])
    return b0.returncode == 0


def compare_printed(ch):
    """Print the statement and definitions with pp.all from the challenge text `ch` and from DistinctDistances.Main."""
    ch_imports = [l for l in ch.splitlines() if l.startswith('import ')]
    ch_body = [l for l in ch.splitlines() if not l.startswith('import ')]
    rc1, a = printed(ch_imports + ch_body)
    rc2, b = printed(['import DistinctDistances.Main'])
    a = a.replace("declaration uses 'sorry'", '').replace('declaration uses `sorry`', '')
    a = '\n'.join(l for l in a.splitlines() if not l.startswith('warning'))
    b = '\n'.join(l for l in b.splitlines() if not l.startswith('warning'))
    same = rc1 == 0 and rc2 == 0 and a.strip() == b.strip() and 'jsp_000900' in a
    print(f'challenge exit {rc1}, main exit {rc2}, pp.all outputs identical: {a.strip() == b.strip()}')
    return same, a, b


def types():
    if not build_main():
        return False
    rc0, ax = axioms_of_main()
    ax_ok = rc0 == 0 and ax is not None and ax <= ALLOWED
    print(f'axioms of DistinctDistances.jsp_000900: {sorted(ax) if ax is not None else "unparsed"}; allowed: {ax_ok}')
    same, a, b = compare_printed((ROOT / 'Challenge.lean').read_text())
    ok = ax_ok and same
    if not ok:
        print('--- challenge\n' + a[-3000:] + '\n--- main\n' + b[-3000:])
    return ok


def statement():
    if not build_main():
        return False
    same, a, b = compare_printed((ROOT / 'Challenge.lean').read_text())
    if not same:
        print('--- challenge\n' + a[-3000:] + '\n--- main\n' + b[-3000:])
    return same


if __name__ == '__main__':
    if len(sys.argv) >= 2 and sys.argv[1] == 'defs':
        sys.exit(0 if defs(sys.argv[2] if len(sys.argv) > 2 else None) else 1)
    if len(sys.argv) == 2 and sys.argv[1] == 'types':
        sys.exit(0 if types() else 1)
    if len(sys.argv) == 2 and sys.argv[1] == 'statement':
        sys.exit(0 if statement() else 1)
    sys.exit(__doc__)
