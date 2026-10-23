module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexGlobalPullbackEndpoints
public import SerrePositivity.InfinityCategories.F1.PullbackCommonNormalizedIso
public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-!
概要：元の全 Hom 上で補正 pullback 比較と元の分類作用の二辺制限を関手同型で結ぶ。
方針：同じ共有頂点の指定像の一致から両端固定の円柱を貼り合わせる。
規約：元の二射を保持し、同値性や持ち上げ性を追加仮定にしない。
使われ方：元の分類 Hom 作用の二単体上の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom に対する補正比較と元の分類作用の二辺制限は、同じ pullback 上で同型。 -/
def cocartesianTwoSimplexGlobalPullbackComparisonIso :
    FunctorIso (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q)
      (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q) := by
  have : Fibration ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl) :=
    fibration_of_kanEquivalenceLifting_of_kanComplex _
      (cocartesianTwoSimplexLocalTarget_first_kanEquivalenceLifting k p q)
  have hL : F2.functorIsoOfEq
      ((cocartesianTwoSimplexGlobalPullbackFirstComponentIso k p q).postcomp
        ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl))
      (cocartesianTwoSimplexGlobalPullbackFirstComponent_shared_source k p q)
      (cocartesianTwoSimplexGlobalPullbackFirstComponent_shared_target k p q) =
      cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q := by
    exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
      (cocartesianTwoSimplexGlobalPullbackFirstComponentIso_shared_heq k p q))
  have hR : F2.functorIsoOfEq
      ((cocartesianTwoSimplexGlobalPullbackSecondComponentIso k p q).postcomp
        ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr))
      (cocartesianTwoSimplexGlobalPullbackSecondComponent_shared_source k p q)
      (cocartesianTwoSimplexGlobalPullbackSecondComponent_shared_target k p q) =
      cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q := by
    exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
      (cocartesianTwoSimplexGlobalPullbackSecondComponentIso_shared_heq k p q))
  exact pullbackFunctorIsoOfCommonNormalizedIsos
    ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)
    ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q)
    (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q)
    (cocartesianTwoSimplexGlobalPullbackFirstComponentIso k p q)
    (cocartesianTwoSimplexGlobalPullbackSecondComponentIso k p q)
    (cocartesianTwoSimplexGlobalPullbackFirstComponent_shared_source k p q)
    (cocartesianTwoSimplexGlobalPullbackFirstComponent_shared_target k p q)
    (cocartesianTwoSimplexGlobalPullbackSecondComponent_shared_source k p q)
    (cocartesianTwoSimplexGlobalPullbackSecondComponent_shared_target k p q)
    (hL.trans hR.symm)

/-- 同じ元の全 Hom 上で、補正比較と元の二辺制限の同値性は同値。 -/
lemma cocartesianTwoSimplexGlobalPullbackMap_isQCatEquivalence_iff :
    IsQCatEquivalence (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q) ↔
      IsQCatEquivalence (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q) := by
  constructor
  · intro h
    exact h.ofFunctorIso (cocartesianTwoSimplexGlobalPullbackComparisonIso k p q)
  · intro h
    exact h.ofFunctorIso (cocartesianTwoSimplexGlobalPullbackComparisonIso k p q).symm

end SerrePositivity.InfinityCategories
