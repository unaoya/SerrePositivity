module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldGlobalPullbackEndpoints
public import SerrePositivity.InfinityCategories.F1.PullbackCommonNormalizedIso
public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-!
概要：元の全 Hom 上で補正 pullback 比較と元の分類作用の最初の辺と尾部制限を関手同型で結ぶ。
方針：同じ共有頂点の指定像の一致から両端固定の円柱を貼り合わせる。
規約：元の二射を保持し、同値性や持ち上げ性を追加仮定にしない。
使われ方：元の分類 Hom 作用の高次単体上の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom に対する補正比較と元の分類作用の最初の辺と尾部制限は、同じ pullback 上で同型。 -/
def cocartesianScaffoldGlobalPullbackComparisonIso :
    FunctorIso (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q)
      (cocartesianScaffoldOriginalGlobalPullbackMap n k p q) := by
  have : Fibration ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl) :=
    fibration_of_kanEquivalenceLifting_of_kanComplex _
      (cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q)
  have hL : F2.functorIsoOfEq
      ((cocartesianScaffoldGlobalPullbackFirstComponentIso n k p q).postcomp
        ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl))
      (cocartesianScaffoldGlobalPullbackFirstComponent_shared_source n k p q)
      (cocartesianScaffoldGlobalPullbackFirstComponent_shared_target n k p q) =
      cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q := by
    exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
      (cocartesianScaffoldGlobalPullbackFirstComponentIso_shared_heq n k p q))
  have hR : F2.functorIsoOfEq
      ((cocartesianScaffoldGlobalPullbackSecondComponentIso n k p q).postcomp
        ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr))
      (cocartesianScaffoldGlobalPullbackSecondComponent_shared_source n k p q)
      (cocartesianScaffoldGlobalPullbackSecondComponent_shared_target n k p q) =
      cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q := by
    exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
      (cocartesianScaffoldGlobalPullbackSecondComponentIso_shared_heq n k p q))
  exact pullbackFunctorIsoOfCommonNormalizedIsos
    ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)
    ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)
    (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q)
    (cocartesianScaffoldOriginalGlobalPullbackMap n k p q)
    (cocartesianScaffoldGlobalPullbackFirstComponentIso n k p q)
    (cocartesianScaffoldGlobalPullbackSecondComponentIso n k p q)
    (cocartesianScaffoldGlobalPullbackFirstComponent_shared_source n k p q)
    (cocartesianScaffoldGlobalPullbackFirstComponent_shared_target n k p q)
    (cocartesianScaffoldGlobalPullbackSecondComponent_shared_source n k p q)
    (cocartesianScaffoldGlobalPullbackSecondComponent_shared_target n k p q)
    (hL.trans hR.symm)

/-- 同じ元の全 Hom 上で、補正比較と元の最初の辺と尾部制限の同値性は同値。 -/
lemma cocartesianScaffoldGlobalPullbackMap_isQCatEquivalence_iff :
    IsQCatEquivalence (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q) ↔
      IsQCatEquivalence (cocartesianScaffoldOriginalGlobalPullbackMap n k p q) := by
  constructor
  · intro h
    exact h.ofFunctorIso (cocartesianScaffoldGlobalPullbackComparisonIso n k p q)
  · intro h
    exact h.ofFunctorIso (cocartesianScaffoldGlobalPullbackComparisonIso n k p q).symm

end SerrePositivity.InfinityCategories
