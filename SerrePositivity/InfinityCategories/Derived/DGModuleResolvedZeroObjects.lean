module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
/-!
概要：任意の実出力分解 ∞ 関手が、元の入力の零頂点を保存することを示す。
方針：同じ入力切断の全 ∞ 同値と、実出力 dg 射影の零性の保存を合成する。
規約：元の出力の射影性は不要。使われ方：一般 kernel の完全性の零条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実入力切断と dg 出力射影は零頂点を保つ。 -/
lemma dgModuleResolvedInfinity_preservesZeroVertices :
    PreservesZeroVertices (dgModuleResolvedInfinity R C E F) := by
  rw [dgModuleResolvedInfinity_eq_section_replacement]
  let S := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  have hS : PreservesZeroVertices S := by
    let := isExactFunctor_of_isQCatEquivalence
      (dgModuleResolvedSourceSection_isQCatEquivalence R C E F)
    exact IsExactFunctor.preservesZero (F := S)
  intro x hx
  exact dgFunctorNerve_preservesZeroVertices
    (dgModuleFunctorResolutionReplacement R C E F) _ (hS x hx)
end SerrePositivity.InfinityCategories
