#!/usr/bin/env python3
"""Focused compiler probes; deliberately not presented as the full A-J audit."""
from pathlib import Path
import difflib
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'audit/realized-constitution'
(OUT/'patches').mkdir(parents=True, exist_ok=True)
(OUT/'logs').mkdir(parents=True, exist_ok=True)
CORE = 'RelationalPerimeter/Computation/ConstitutiveSearch/RelationalProfileConstitution.lean'
ROLES = 'RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProfiles.lean'
core = (ROOT/CORE).read_text()
roles = (ROOT/ROLES).read_text()

def one(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'Probe does not match the checked implementation: {old[:80]}')
    return text.replace(old, new, 1)

probes = [('CoreControl', CORE, core, core, True,
           'Unmodified generic module in the same disposable-file setup'),
          ('RoleControl', ROLES, roles, roles, True,
           'Unmodified role module in the same disposable-file setup')]

ignored = one(roles, '  evidence.formationWitness.2.down ▸ value', '  value')
ignored = one(ignored,
    '    (evidence : RoleConstitutionEvidence role identity)\n    (value : Motive identity.realized.state)',
    '    (_evidence : RoleConstitutionEvidence role identity)\n    (value : Motive identity.realized.state)')
probes.append(('FormationTransportIgnored', ROLES, roles, ignored, False,
               'The generic input fibre cannot be returned in the output fibre without formation transport'))

replacement = one(core,
    '  change constituteRealizedOccurrence stage\n    (stage.realize (stage.classify identity.realized)) = identity\n  rw [stage.realize_classify identity.realized]\n  exact identity.reconstitute',
    '  rfl')
probes.append(('RealizationReturnLawIgnored', CORE, core, replacement, False,
               'The occurrence return law is no longer a position-wrapper reflexivity proof'))

noformation = one(roles, '  formedAt : state = position.state role\n', '')
noformation = one(noformation, '\n    formedAt := rfl }', ' }')
noformation = one(noformation,
    '  | mk position state formedAt =>\n      cases formedAt\n      rfl',
    '  | mk position state =>\n      rfl')
probes.append(('RawFormationErased', ROLES, roles, noformation, False,
               'Coherent deletion of the intrinsic formation field and its constructor argument loses exact realization'))

recovered = one(roles,
    '  evidence.formationWitness.2.down ▸ value',
    '  identity.realized.formedAt ▸ value')
recovered = one(recovered,
    '    (evidence : RoleConstitutionEvidence role identity)\n    (value : Motive identity.realized.state)',
    '    (_evidence : RoleConstitutionEvidence role identity)\n    (value : Motive identity.realized.state)')
probes.append(('FormationRecoveredFromRealization', ROLES, roles, recovered, True,
               'Positive control: recovering the same formation agreement from the realized occurrence is not erasure of that agreement'))

report = {
    'source_commit': subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip(),
    'scope': 'Focused module-compilation probes with unmodified controls; not coherent whole-repository A-J mutation certification.',
    'full_mutation_builds_and_both_verifiers': 'NOT RUN for these isolated module probes',
    'results': []
}
failed = False
with tempfile.TemporaryDirectory(prefix='realized-constitution-probes-') as directory:
    for name, path, before, after, should_compile, purpose in probes:
        probe = Path(directory)/f'{name}.lean'
        probe.write_text(after)
        patch = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                     fromfile='a/'+path, tofile='b/'+path))
        if patch:
            (OUT/'patches'/f'{name}.patch').write_text(patch)
        command = ['lake','env','lean',str(probe)]
        try:
            run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, timeout=240)
            code, output = run.returncode, run.stdout
        except subprocess.TimeoutExpired as exc:
            code, output = 124, 'TIMEOUT: not a substantive rejection\n'+str(exc)
        errors = [line for line in output.splitlines() if 'error:' in line or 'warning:' in line]
        substantive = code not in (0,124,127) and any(
            marker in output.lower() for marker in ('type mismatch','tactic `rfl` failed','not definitionally equal','unsolved goals'))
        outcome_ok = (code == 0) if should_compile else substantive
        failed |= not outcome_ok
        (OUT/'logs'/f'{name}.log').write_text(output)
        report['results'].append({
            'name': name, 'module': path, 'purpose': purpose,
            'expected': 'COMPILES' if should_compile else 'SUBSTANTIVE TYPE OR PROOF REJECTION',
            'exit_code': code, 'expectation_met': outcome_ok,
            'substantive_rejection': substantive,
            'diagnostics': errors[:12], 'output_head': output.splitlines()[:45],
            'patch': f'patches/{name}.patch' if patch else None
        })
        print(name, 'exit', code, 'expectation_met', outcome_ok, flush=True)
        for error in errors[:5]: print(error, flush=True)
(OUT/'dependency-probes.json').write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
raise SystemExit(1 if failed else 0)
