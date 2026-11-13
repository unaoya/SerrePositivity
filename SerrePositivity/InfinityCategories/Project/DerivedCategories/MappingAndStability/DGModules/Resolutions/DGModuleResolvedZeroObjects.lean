module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ実入力切断と dg 出力射影は零頂点を保つ。 -/
lemma dgModuleResolvedInfinity_preservesZeroVertices :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement]
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices S := by
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSection_isQCatEquivalence R C E F)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := S)
  intro x hx
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F) _ (hS x hx)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
