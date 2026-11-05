import Operad

/-! Axiom sweep. `Audit.lean` prints the axioms of selected declarations; this file checks
*every* constant defined in an `Operad` module, private and auxiliary ones included, and fails if
any rests on an axiom other than Lean's three standard ones (`propext`, `Classical.choice`,
`Quot.sound`). A declared `axiom` depends on itself, so it fails here too. Like `Audit.lean`, it is
outside the `Operad` lean_lib; CI runs it with `lake env lean AxiomSweep.lean`. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (nm, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? nm | continue
    unless (`Operad).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    n := n + 1
    let extra := (← liftCoreM <| Lean.collectAxioms nm).filter (!std.contains ·)
    unless extra.isEmpty do bad := bad.push (nm, extra)
  if bad.isEmpty then
    logInfo m!"{n} constants checked; all rest only on propext, Classical.choice, Quot.sound."
  else
    let shown := MessageData.joinSep
      (bad.toList.take 50 |>.map fun (nm, axs) => m!"\n  {nm}: {axs}") ""
    throwError m!"{bad.size} of {n} constants rest on non-standard axioms:{shown}"
