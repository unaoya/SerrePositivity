module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OrdinaryPullbackStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OrdinaryPullbackFlatQuotient
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseVertexClosure
/-!
概要：通常 pullback の対象条件は、元 gluing 内で実安定閉包を取っても変わらない。
方針：正本比較と差の完全関手を合成し、安定閉包の全対象の零化を検出する。
規約：元の対象条件と元の nerve の安定閉包を比較する。
使われ方：D-9 の実小核と通常 pullback を零化する商の一致に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
def dgGluingPullbackDifference :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    laxDifference
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD))
include hC hD
lemma dgGluingPullbackDifference_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgGluingPullbackDifference R C D M hC hD) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor R C D M
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
lemma dgGluingPullbackProperty_iff_difference_zero (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M X ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgGluingPullbackDifference R C D M hC hD).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) := by
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableYonedaMap R C hC
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
  let q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableCoefficientMap R C D M hD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty_iff_laxVertex R C D M X).trans
    (laxDifference_zero_iff p q
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)))).symm
lemma dgGluingPullbackProperty_stableClosure_iff (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M) X ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M X := by
  constructor
  · intro hx
    let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerve_isStable R C D M hC hD
    let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableModuleCategory.{u, v, w} R C).isStable
    let := dgGluingPullbackDifference_isExactFunctor R C D M hC hD
    apply (dgGluingPullbackProperty_iff_difference_zero R C D M hC hD X).mpr
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure (dgGluingPullbackDifference R C D M hC hD)
      (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPullbackProperty R C D M))) _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.ulift _ hx)
    rintro _ ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    exact (dgGluingPullbackProperty_iff_difference_zero R C D M hC hD Y).mp hY
  · intro hx
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨X, hx, rfl⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
