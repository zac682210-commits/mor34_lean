#!/usr/bin/env python3
"""Four fail-closed readiness gates. No proof progress is inferred from templates."""
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / 'logs' / 'environment_gate'
LOGS.mkdir(parents=True, exist_ok=True)
os.chdir(ROOT)
result = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'ready': False, 'steps': [], 'scope': 'Project build and explicit named-theorem axiom audit; consult docs/ACCEPTANCE.json for verified paper scope'}

def save():
    result['updated_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (LOGS / 'result.json').write_text(json.dumps(result, indent=2) + '\n')

def run(name, args):
    exe = shutil.which(args[0])
    try:
        if exe is None:
            raise FileNotFoundError(f'{args[0]} is not installed or not on PATH')
        with (LOGS / f'{name}.log').open('w', encoding='utf-8') as f:
            p = subprocess.run([exe, *args[1:]], stdout=f, stderr=subprocess.STDOUT,
                               text=True, timeout=1800)
        code = p.returncode
    except (OSError, subprocess.TimeoutExpired) as e:
        (LOGS / f'{name}.log').write_text(str(e) + '\n')
        code = -1
    result['steps'].append({'name': name, 'command': args, 'exit_code': code})
    save()
    print(f'{name}: {"PASS" if code == 0 else "FAIL"}', flush=True)
    if code:
        print((LOGS / f'{name}.log').read_text(errors='replace'))
        raise SystemExit(1)

save()
run('1_lean_version', ['lean', '--version'])
version = (LOGS / '1_lean_version.log').read_text()
if 'version 4.19.0,' not in version:
    result['version_mismatch'] = version
    save()
    sys.exit('Wrong Lean version: expected 4.19.0')
run('2_core_smoke', ['lean', 'smoke/Minimal.lean'])
run('dependencies', ['lake', 'update'])
run('cache', ['lake', 'exe', 'cache', 'get'])
run('3_mathlib_smoke', ['lake', 'env', 'lean', 'smoke/Mathlib.lean'])
run('4_project_build', ['lake', 'build'])
run('4_computed_normals_smoke', ['lake', 'env', 'lean', 'smoke/ComputedNormals.lean'])
run('4_project_axioms', ['lake', 'env', 'lean', 'Check.lean'])
run('4_axiom_allowlist', [sys.executable, 'scripts/audit_axioms.py',
                         str(LOGS / '4_project_axioms.log')])
result['ready'] = True
save()
print('Environment gates passed. This does not prove the MOR34 main theorem.')
