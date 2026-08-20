import EM
/-! Whole-library axiom gate.  Run from the repo root after `lake build`:

      lake env lean tools/lean/AxiomGate.lean

Walks every constant whose defining module is `EM` or `EM.*` (i.e. the whole `lean_lib EM`
import closure; `EM/Archive/` is not imported and `EMRegistry` is not in scope) and reports any
that depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`.  This covers
`sorryAx`, `Lean.ofReduceBool` (native_decide) and user axioms.  Exit code 1 on any offender.
`tools/check_axioms.py` runs this and additionally checks the registry-published set. -/
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def isEMModule (n : Name) : Bool :=
  n == `EM || (`EM).isPrefixOf n

#eval show CoreM Unit from do
  let env ← getEnv
  let mut checked := 0
  let mut bad : Array (Name × List Name) := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      if !isEMModule env.header.moduleNames[idx.toNat]! then continue
      checked := checked + 1
      let axs ← collectAxioms n
      let extra := axs.toList.filter (fun a => !allowed.contains a)
      if extra.length > 0 then bad := bad.push (n, extra)
  IO.println s!"AxiomGate: checked {checked} EM declarations; {bad.size} with non-standard axioms"
  for (n, ax) in bad do
    IO.println s!"  {n}: {ax}"
  if bad.size > 0 then
    throwError "AxiomGate: non-standard axioms found"
