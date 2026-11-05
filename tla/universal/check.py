#!/usr/bin/env python3
# Copyright (c) 2026 Eric Spencer. Released under Apache 2.0 license.
"""Check universal semantics and generated modules without compiling on the coordinator."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
os.chdir(root)
sys.path.insert(0, str(root.parent))
from universal_compile import compile_file

lake = os.environ.get('LAKE', 'lake')
subprocess.run([lake, 'build'], check=True)
fixtures = ['Counter.tla'] + [
    str(p.relative_to(root.parent / 'tests'))
    for p in sorted((root.parent / 'tests' / 'fixtures').rglob('*.tla'))
    if p.name != 'FalseClaim.tla'  # Checked separately as a rejected certificate.
]
fixtures += [str(p.relative_to(root.parent / 'tests')) for p in sorted((root.parent / 'tests' / 'corpus').glob('*.tla'))]
failures = []
with tempfile.TemporaryDirectory(prefix='universal-check-', dir='.') as directory:
    for fixture in fixtures:
        source = root.parent / 'tests' / fixture
        target = Path(directory) / source.with_suffix('.lean').name
        code = compile_file(source, includes=[root.parent / 'tests' / 'corpus' / 'tlaps', root.parent / 'tests' / 'corpus' / 'community'])
        code += '\nopen TLAImported\n'
        if source.name == 'TheoremArgument.tla':
            code += '\nexample (c : TheoremArgument.Constants) (b : Behavior) (n : Nat) : truth (TheoremArgument.Law c b n) := by\n  simp [TheoremArgument.Law, truth_boolean]\n'
        if source.name == 'HigherRecursive.tla':
            code += '\nexample (c : HigherRecursive.Constants) (b : Behavior) (n : Nat) : truth (HigherRecursive.BaseLaw c b n) := by\n  simp only [HigherRecursive.BaseLaw, truth_boolean]\n  apply higherRecursiveOperator_base\n  intro g\n  simp only [truth, if_pos rfl, realBinary_add_integer]\n  rfl\n'
            code += '\nexample (c : HigherRecursive.Constants) (b : Behavior) (n : Nat) : HigherRecursive.Zero c b n = integer 7 := by\n  unfold HigherRecursive.Zero\n  apply higherRecursiveOperator_base\n  intro g\n  simp [truth_boolean]\nexample (c : HigherRecursive.Constants) (b : Behavior) (n : Nat) : truth (HigherRecursive.ForwardedLaw c b n) := by\n  simp only [HigherRecursive.ForwardedLaw, HigherRecursive.Forwarded, truth_boolean]\n  apply recursiveOperator_base\n  intro g\n  simp [truth]\n'
        if source.name == 'ClosedImport.tla':
            helpers = [line.split()[1] for line in code.splitlines() if line.startswith('def «')]
            code += '\nexample (c : ClosedImport.Constants) (b : Behavior) (n : Nat) : truth (ClosedImport.Law c b n) := by\n  simp [' + ', '.join([*['ClosedImport.' + h for h in helpers], 'truth_boolean']) + ']\n'
        if source.name == 'Bundled.tla':
            code += '\nexample (c : Bundled.Constants) (b : Behavior) (n : Nat) : truth (Bundled.Answer c b n) := by\n  rfl\n'
        if source.name == 'ParameterizedClaims.tla':
            code += '\nexample (c : ParameterizedClaims.Constants) : ParameterizedClaims.Certificate c := by\n  constructor; intros; simp [ParameterizedClaims.TLAProofClaim0, truth_boolean]\n'
        if source.name == 'OperatorArguments.tla':
            code += '\nexample (c : OperatorArguments.Constants) (b : Behavior) (n : Nat) : truth (OperatorArguments.PlusLaw c b n) := by\n  simp only [OperatorArguments.PlusLaw, OperatorArguments.Plus, truth_boolean, realBinary_add_integer]; rfl\nexample (c : OperatorArguments.Constants) (b : Behavior) (n : Nat) : truth (OperatorArguments.IntersectionLaw c b n) := by\n  simp [OperatorArguments.IntersectionLaw, OperatorArguments.Intersection, truth_boolean, mem_enumerate]\n'
        if source.name == 'Names.tla':
            code += '\nexample (c : Names.Constants_) (b : Behavior) (n : Nat) : truth (Names.LocalNames c b n) := by\n  simp [Names.LocalNames, Names.n, Names.c, Names.b, truth_boolean]\n'
        if source.name == 'CustomArithmetic.tla':
            code += '\nexample (c : CustomArithmetic.Constants) (b : Behavior) (n : Nat) : truth (CustomArithmetic.Law c b n) := by\n  simp [CustomArithmetic.Law, CustomArithmetic.«+», truth_boolean]\n'
        if source.name == 'CustomNumbers.tla':
            code += '\nexample (c : CustomNumbers.Constants) (b : Behavior) (n : Nat) : truth (CustomNumbers.Member c b n) := by\n  simp [CustomNumbers.Member, CustomNumbers.Int, truth_boolean, mem_enumerate]\n'
        if source.name == 'Bool.tla':
            code += '\nexample (c : TLAImported.Bool.Constants) : TLAImported.Bool.Certificate c := by\n  constructor; intros; rfl\n'
        if source.name == 'ArithmeticOperations.tla':
            code += "\nexample (c : ArithmeticOperations.Constants) (b : Behavior) (n : Nat) : truth (ArithmeticOperations.DivisionLaw c b n) := by\n  simp [ArithmeticOperations.DivisionLaw, truth_boolean, intBinary_integer, realNegate_integer, integer_mem, toInt_integer]\n"
        if source.name == 'NestedCalls.tla':
            code += "\nexample (c : NestedCalls.Constants) (b : Behavior) (n : Nat) : NestedCalls.Answer c b n = integer 3 := by\n  simp only [NestedCalls.Answer, realBinary_add_integer]; rfl\nexample (c : NestedCalls.Constants) (b : Behavior) (n : Nat) : NestedCalls.Higher c b n = integer 2 := by\n  simp only [NestedCalls.Higher, realBinary_add_integer]; rfl\n"
        if source.name == 'NestedModules.tla':
            code += "\nexample (c : NestedModules.Constants) (b : Behavior) (n : Nat) : NestedModules.Answer c b n = integer 8 := by\n  simp only [NestedModules.Answer, NestedModules.«I!Value», realBinary_add_integer]; rfl\nexample (c : NestedModules.Constants) (b : Behavior) (n : Nat) : NestedModules.Next c b n = boolean (b (n+1) \"x\" = realBinary (fun a b => a+b) (b n \"x\") (integer 1)) := rfl\n"
        if source.name == 'SequenceOperations.tla':
            code += "\nexample (c : SequenceOperations.Constants) (b : Behavior) (n : Nat) : truth (SequenceOperations.LengthLaw c b n) := by\n  simp only [SequenceOperations.LengthLaw, SequenceOperations.Length, SequenceOperations.S, truth_boolean, length_tuple]; rfl\nexample (c : SequenceOperations.Constants) (b : Behavior) (n : Nat) : truth (SequenceOperations.FirstLaw c b n) := by\n  simp only [SequenceOperations.FirstLaw, SequenceOperations.First, SequenceOperations.S, truth_boolean]\n  exact apply_tuple [integer 1, ZFSet.zftrue, string \"x\"] 0 (by decide)\n"
        if source.name == 'ToolDefinitions.tla':
            code += "\nexample (c : ToolDefinitions.Constants) (b : Behavior) (n : Nat) : ToolDefinitions.Printed c b n = integer 42 := rfl\nexample (c : ToolDefinitions.Constants) (b : Behavior) (n : Nat) : ToolDefinitions.Evaluated c b n = integer 42 := rfl\n"
        if source.name == 'Binders.tla':
            code += (root / 'BindersProof.txt').read_text()
        if source.name == 'Counter.tla':
            code += (root / 'CounterProof.txt').read_text() + (root / 'NativeCounterProof.txt').read_text()
        if source.name == 'Temporal.tla':
            code += (root / 'TemporalProof.txt').read_text()
        if source.name == 'ValueLaws.tla':
            code += (root / 'ValueProof.txt').read_text()
        if source.name == 'ProofInstance.tla':
            code += "\nexample (c : ProofInstance.Constants) : ProofInstance.Certificate c := by\n  constructor <;> intros <;> simp [ProofInstance.TLAProofClaim0, truth_boolean]\n"
        if source.name == 'LevelClaims.tla':
            code += "\nexample (c : LevelClaims.Constants) : LevelClaims.Certificate c := by\n  constructor <;> intros <;> simp [LevelClaims.TLAProofClaim0, LevelClaims.TLAProofClaim1, LevelClaims.TLAProofClaim2, LevelClaims.TLAProofClaim3, LevelClaims.TLAProofClaim4, LevelClaims.TLAProofClaim5, truth_boolean]\n"
        if source.name == 'HigherOrder.tla':
            code += "\nexample (c : HigherOrder.Constants) (b : Behavior) (n : Nat) : HigherOrder.Answer c b n = integer 3 := by simp only [HigherOrder.Answer, realBinary_add_integer]; rfl\nexample (c : HigherOrder.Constants) (b : Behavior) (n : Nat) : HigherOrder.ConstantCall c b n = c.F (integer 2) := rfl\n"
        if source.name == 'Labels.tla':
            code += "\nexample (c : Labels.Constants) (b : Behavior) (n : Nat) : truth (Labels.B c b n) := by simp [Labels.B, truth_boolean]\n"
        if source.name == 'Recursive.tla':
            code += (root / 'RecursiveProof.txt').read_text()
        if source.name == 'NumericDomains.tla':
            code = code.replace('import TLAUniversal', 'import TLAUniversal\nimport Mathlib.Tactic.NormNum')
            code += (root / 'NumericProof.txt').read_text()
        if source.name == 'RealNumbers.tla':
            code = code.replace('import TLAUniversal', 'import TLAUniversal\nimport Mathlib.Tactic.NormNum')
            code += (root / 'RealProof.txt').read_text()
        if source.name == 'StructuredClaims.tla':
            code += "\nexample (c : StructuredClaims.Constants) : StructuredClaims.Certificate c := by\n  constructor <;> intros <;> simp [StructuredClaims.TLAProofClaim0, StructuredClaims.TLAProofClaim1, truth_boolean]\n"
        target.write_text(code)
        result = subprocess.run([lake, 'env', 'lean', str(target)], capture_output=True, text=True, timeout=120)
        if result.returncode:
            failures.append(fixture)
            print(result.stdout + result.stderr, flush=True)
        if source.name == 'Counter.tla' and result.returncode == 0:
            subprocess.run([lake, 'env', 'lean', '--root=' + directory, '-o', str(target.with_suffix('.olean')), str(target)], check=True, capture_output=True, text=True, timeout=120)
            consumer = Path(directory) / 'Consumer.lean'
            consumer.write_text('module\nimport Counter\nopen TLAUniversal\n' + (root / 'CounterProof.txt').read_text() + (root / 'NativeCounterProof.txt').read_text())
            import_env = dict(os.environ)
            import_env['LEAN_PATH'] = str(Path(directory).resolve()) + os.pathsep + import_env.get('LEAN_PATH', '')
            imported = subprocess.run([lake, 'env', 'lean', str(consumer)], env=import_env, capture_output=True, text=True, timeout=120)
            if imported.returncode:
                failures.append('Counter consumer import')
                print(imported.stdout + imported.stderr, flush=True)
        print(('FAIL ' if result.returncode else 'PASS ') + fixture, flush=True)
    # The proof CLI writes an artifact only after Lean accepts its proof terms.
    proof_output = Path(directory) / 'CheckedProofs.lean'
    proof_sources = [root.parent / 'tests/proofs' / (name + '.tla') for name in
                     ('Fairness', 'FunctionRange', 'RecordEquality', 'imported/ImportedLaw', 'TemporalInduction', 'StateGeneralization', 'NaturalInduction', 'CaseReferences', 'Leaves', 'ProofShapes', 'DefinitionScope', 'Arithmetic', 'LocalDefinition', 'LevelBinders', 'Foundation', 'BoundedWitness', 'TupleBinders', 'SymbolicArithmetic', 'InstanceBinding', 'ModuleUse')]
    proof_sources += sorted((root.parent / 'tests/proofs/upstream').glob('*.tla'))
    for proof_source in proof_sources:
        proof_fixture = proof_source.stem
        proved = subprocess.run([sys.executable, str(root.parent / 'prove.py'),
                                 str(proof_source), '--timeout', '45', '-I', str(root.parent / 'tests/corpus/tlaps'),
                                 '-o', str(proof_output)],
                                capture_output=True, text=True, timeout=150)
        if proved.returncode:
            failures.append('source proof reconstruction: ' + proof_fixture)
            print(proved.stdout + proved.stderr, flush=True)
        else:
            subprocess.run([lake, 'env', 'lean', '--root=' + directory,
                            '-o', str(proof_output.with_suffix('.olean')), str(proof_output)],
                           check=True, capture_output=True, text=True, timeout=120)
            consumer = Path(directory) / 'ProofConsumer.lean'
            namespace = next(line.removeprefix('namespace ') for line in proof_output.read_text().splitlines()
                             if line.startswith('namespace TLAImported.'))
            consumer.write_text('module\nimport CheckedProofs\n'
                                + f'example (c : {namespace}.Constants) : '
                                + f'{namespace}.Certificate c := '
                                + f'{namespace}.TLACheckedCertificate c\n')
            import_env = dict(os.environ)
            import_env['LEAN_PATH'] = str(Path(directory).resolve()) + os.pathsep + import_env.get('LEAN_PATH', '')
            imported = subprocess.run([lake, 'env', 'lean', str(consumer)], env=import_env,
                                      capture_output=True, text=True, timeout=120)
            if imported.returncode:
                failures.append('proof certificate consumer: ' + proof_fixture)
                print(imported.stdout + imported.stderr, flush=True)
            print('PASS source proof reconstruction: ' + proof_fixture, flush=True)
    negative_sources = [root.parent / 'tests/proofs' / (name + '.tla') for name in ('FalseFairness', 'FalseFunctionRange', 'FalseRecordEquality', 'imported/FalseImportedLaw', 'FalseTemporalInduction', 'FalseStateGeneralization', 'FalseInduction', 'FalseHave', 'FalseCaseReferences', 'FalseChoice', 'FalseLeaf', 'FalseStep', 'FalseArithmetic', 'FalseSymbolicArithmetic', 'FalseWitness', 'FalseModuleUse', 'Omitted')]
    negative_sources += sorted((root.parent / 'tests/proofs/negative').glob('*.tla'))
    for negative_source in negative_sources:
        proof_fixture = negative_source.stem
        proof_output.write_text('preserve existing output')
        rejected = subprocess.run([sys.executable, str(root.parent / 'prove.py'),
                                   str(negative_source), '--timeout', '15', '-I', str(root.parent / 'tests/corpus/tlaps'),
                                   '-o', str(proof_output)],
                                  capture_output=True, text=True, timeout=150)
        if rejected.returncode == 0 or proof_output.read_text() != 'preserve existing output':
            raise RuntimeError('invalid source proof accepted or replaced output: ' + proof_fixture)
    # SANY accepts proof hints without checking them. They must never become
    # trusted Lean proofs or make a source certificate trivially inhabited.
    target = Path(directory) / 'FalseClaim.lean'
    code = compile_file(root.parent / 'tests' / 'fixtures' / 'FalseClaim.tla')
    target.write_text(code + "\nexample (c : TLAImported.FalseClaim.Constants) : TLAImported.FalseClaim.Certificate c := by\n  constructor; intros; simp [TLAImported.FalseClaim.TLAProofClaim0, truth, ZFSet.zftrue_ne_zffalse]\n")
    result = subprocess.run([lake, 'env', 'lean', str(target)], capture_output=True, text=True, timeout=120)
    if result.returncode == 0 or 'unsolved goals' not in result.stdout:
        raise RuntimeError('false source proof certificate was not rejected: ' + result.stdout + result.stderr)
    target = Path(directory) / 'Negative.lean'
    target.write_text('module\nimport TLAUniversal\nexample : TLAUniversal.truth (TLAUniversal.boolean False) := by simp [TLAUniversal.truth_boolean]\n')
    result = subprocess.run([lake, 'env', 'lean', str(target)], capture_output=True, text=True)
    if result.returncode == 0 or 'error:' not in result.stdout:
        raise RuntimeError('false universal-value proof was not rejected')
if failures:
    raise RuntimeError('Universal checks failed: ' + ', '.join(failures))
print('Universal definitions, generated modules and negative proof checks passed.')
