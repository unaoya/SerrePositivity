module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomOverRestriction

/-!
概要：底上の局所自然性の両端と正規化後の指定値を分離する。
方針：同じ制限の正規化等式だけで既存の自然性の端点を移す。
規約：元の全 Hom と指定同型を保持する。
使われ方：充満忠実な後合成による指定値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の直接底変換からの局所比較。 -/
def cocartesianLocalHomOverNaturalitySource :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
      (cocartesianBaseChangeOverMap l k))) ≫ cocartesianLocalHomComparison (l ⋙ k) p q

/-- 同じ底上の射による標的の局所制限。 -/
def cocartesianLocalHomOverNaturalityTarget :=
  cocartesianLocalHomComparison k p q ≫
    intervalDiagramOverPre
      (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (a := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k))))
      (b := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)))
      (uliftOverMorphism (cocartesianBaseChangeOverMap l k))

/-- 既存の同型な端点正規化は充満忠実。 -/
lemma cocartesianLocalHomOverNormalization_isFullyFaithful :
    IsFullyFaithful (cocartesianBaseChangeHomCompositionNormalization l k p q) :=
  (qCatEquivalenceOfIso
    (asIso (cocartesianBaseChangeHomCompositionNormalization l k p q))).isQCatEquivalence.isFullyFaithful

/-- 標的の制限は同じ正規化後に既存の制限と一致する。 -/
lemma cocartesianLocalHomOverNaturalityTarget_normalization :
    (cocartesianLocalHomComparison_nativeRestrictionIso l k p q).targetMap =
      cocartesianLocalHomOverNaturalityTarget l k p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q := by
  exact (congrArg (fun r ↦ cocartesianLocalHomComparison k p q ≫ r)
    (cocartesianLocalHomOverRestriction_normalization l k p q).symm).trans
      (Category.assoc _ _ _).symm

/-- 元の指定自然性の端点だけを正規化した逆像の入力。 -/
def cocartesianLocalHomOverNaturalityInputIso :
    FunctorIso
      (cocartesianLocalHomOverNaturalitySource l k p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q)
      (cocartesianLocalHomOverNaturalityTarget l k p q ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q) :=
  F2.functorIsoOfEq (cocartesianLocalHomComparison_nativeRestrictionIso l k p q)
    rfl (cocartesianLocalHomOverNaturalityTarget_normalization l k p q)

end SerrePositivity.InfinityCategories
