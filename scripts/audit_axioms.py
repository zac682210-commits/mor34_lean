#!/usr/bin/env python3
"""Fail-closed audit of the three named #print axioms outputs.
This is a log check, not a substitute for Lean or independent replay.
"""
import pathlib
import re
import sys

EXPECTED = {
    'MOR34.balancedSplit',
    'MOR34.one_feasible_of_pair_sum',
    'MOR34.balanced_values_are_tight',
    'MOR34.interior_cut_arithmetic',
}
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}

def audit(text):
    seen = set()
    for name in EXPECTED:
        quoted = re.escape(name)
        empty = re.search(r"['‘]?" + quoted + r"['’]? does not depend on any axioms", text)
        nonempty = re.search(r"['‘]?" + quoted + r"['’]? depends on axioms:\s*\[([^\]]*)\]", text)
        if empty:
            seen.add(name)
        elif nonempty:
            actual = {a.strip() for a in nonempty.group(1).split(',') if a.strip()}
            if not actual <= ALLOWED:
                raise ValueError(f'{name}: non-allowlisted dependencies: {sorted(actual - ALLOWED)}')
            seen.add(name)
        else:
            raise ValueError(f'Missing or unrecognized axiom output for {name}')
    if 'sorryAx' in text:
        raise ValueError('sorryAx appears in audit output')
    return seen

if __name__ == '__main__':
    try:
        checked = audit(pathlib.Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as e:
        print(f'REJECTED: {e}', file=sys.stderr)
        sys.exit(1)
    print('Allowed axiom dependencies for:', ', '.join(sorted(checked)))
