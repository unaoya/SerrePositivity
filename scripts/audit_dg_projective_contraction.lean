import SerrePositivity.DifferentialGraded.Derived.Basic
import Lean

/-! 新葉の全宣言を標準三公理で監査し、明示境界の公開型を照合する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `SerrePositivity.DifferentialGraded.Derived.Basic
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.modules[index.toNat]!.module == target do continue
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Forbidden axiom {dependency} in {name}"
    count := count + 1
  unless count > 0 do throwError "No declarations checked in {target}"
  logInfo m!"Projective contraction audit passed: {count} declarations."

open CategoryTheory SerrePositivity.DifferentialGraded
universe u v

example (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (M : RightModule R D)
    (hM : moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R) M))
    (hA : moduleAcyclic R D (ForgetEnrichment.of (Complex R) M)) :
    ∃ H : GradedHom R M M (-1),
      (homObject R (RightModule R D) M M).d (-1) 0 H = (unitElement R M).val :=
  moduleHomotopicallyProjective_contractingElement_of_acyclic R D M hM hA

#print axioms moduleHomotopicallyProjective_contractingElement_of_acyclic
