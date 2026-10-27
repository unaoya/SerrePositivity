import SerrePositivity.DifferentialGraded.Morita.PerfectProjectiveImage
import Lean

/-! 全公開補題と補助宣言を標準三公理で監査し、K-S• の元の全称型を照合する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `SerrePositivity.DifferentialGraded.Morita.PerfectProjectiveImage
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
  logInfo m!"Perfect-projective image audit passed: {count} declarations."

open CategoryTheory SerrePositivity.DifferentialGraded
universe u v w

-- 元の依頼型。対象宇宙は独立で、全加群圏の Small や T の追加保存性は要求しない。
example : ∀ (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] [Small.{u} D]
    (E : Type w) [DGCategory R E] [Small.{u} E]
    (T : DGFunctor R (RightModule R D) (RightModule R E)),
    (∀ d : D, modulePerfectProjectiveOver R E Set.univ (T.obj (representable R d))) →
    ∀ M : RightModule R D, modulePerfectProjectiveOver R D Set.univ M →
      modulePerfectProjectiveOver R E Set.univ (T.obj M) := by
  intro R _ D _ _ E _ _ T hgen M hM
  exact Morita.perfectDGFunctorImage_perfectProjective R D E T hgen hM

#check Morita.perfectDGFunctorImage_perfectProjective
#print axioms Morita.perfectDGFunctorImage_projective_finiteCell
#print axioms Morita.perfectDGFunctorImage_projective
#print axioms Morita.perfectDGFunctorImage_perfectProjective
