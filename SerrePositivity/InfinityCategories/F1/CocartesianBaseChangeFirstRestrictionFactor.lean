module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeRestrictionSquareIdentity
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionRestrictionCoherence

/-!
概要：第一辺の制限因子を元の全 Hom 上で同じ制限正方形の両端へ正規化する。
方針：同じ比較 span の指定切断と厳密な制限の両射影を使う。
規約：元の全 Hom 作用と指定因子比較の値を保持する。
使われ方：元の大域自然性と第一辺の制限自然性の貼り合わせ。
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

/-- 元の比較 span の一射影は同値。 -/
lemma cocartesianBaseChangeHomSpanOne_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeHomSpanOne k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact isQCatEquivalence_of_trivialKanFibration _

/-- 元の大域 Hom 比較を制限した上での、同じ第一辺の指定因子比較。 -/
def cocartesianBaseChangeRestrictedGlobalFactorIso :
    FunctorIso
      (((cocartesianBaseChangeHomComparison k p q ≫
        cocartesianBaseChangeRestrictedHomMap l k p q) ≫
          cocartesianBaseChangeRestrictedHomSpanOne l k p q) ≫
            cocartesianBaseChangeRestrictedHomTransport l k p q)
      ((cocartesianBaseChangeHomComparison k p q ≫
        cocartesianBaseChangeRestrictedHomMap l k p q) ≫
          cocartesianBaseChangeRestrictedHomSpanZero l k p q) :=
  homSpanSectionTransportFactorIso
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeRestrictedHomMap l k p q)

/-- 同じ因子比較の始点は、元の一評価を制限した後の同じ指定輸送。 -/
lemma cocartesianBaseChangeRestrictedGlobalFactor_source :
    (((cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeRestrictedHomMap l k p q) ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q) ≫
          cocartesianBaseChangeRestrictedHomTransport l k p q) =
    (((cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanOne k p q) ≫
      cocartesianBaseChangeHomRestrictionOne l k p q) ≫
        cocartesianBaseChangeRestrictedHomTransport l k p q) := by
  simp only [Category.assoc, cocartesianBaseChangeHomRestrictionOne,
    cocartesianBaseChangeRestrictedHomMap_one]

/-- 同じ因子比較の終点は、元の零評価を同じ底で制限した作用。 -/
lemma cocartesianBaseChangeRestrictedGlobalFactor_target :
    (cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeRestrictedHomMap l k p q) ≫
        cocartesianBaseChangeRestrictedHomSpanZero l k p q =
    (cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanZero k p q) ≫
      cocartesianBaseChangeHomRestrictionZero l k p q := by
  simp only [Category.assoc, cocartesianBaseChangeHomRestrictionZero,
    cocartesianBaseChangeRestrictedHomMap_zero]

/-- 同じ制限正方形の両端へ正規化した、元の第一辺の指定因子比較。 -/
def cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso :
    FunctorIso
      (((cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanOne k p q) ≫
        cocartesianBaseChangeHomRestrictionOne l k p q) ≫
          cocartesianBaseChangeRestrictedHomTransport l k p q)
      ((cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanZero k p q) ≫
        cocartesianBaseChangeHomRestrictionZero l k p q) :=
  F2.functorIsoOfEq (cocartesianBaseChangeRestrictedGlobalFactorIso l k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_source l k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_target l k p q)

/-- 同じ端点の正規化は、元の指定因子の値を保持する。 -/
lemma cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso_heq :
    HEq (cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso l k p q)
      (cocartesianBaseChangeRestrictedGlobalFactorIso l k p q) := by
  exact F2.functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories
