module
public import SerrePositivity.KST.SConstruction.ClosedUnitEvaluation
public import SerrePositivity.KST.SConstruction.SExactFamilyAction

/-! # 元の S₁ 比較と全完全関手族
概要：元の第一行と単位 Hom による S₁ 比較は、全完全関手族に厳密に自然である。
方針：元の比較を同じ固定添字での評価へ因子化して閉 Hom の全族合成式を使う。
規約：逆射を選択しない。使われ方：有限反復と native dg 入力上の構造写像比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の S₁ 比較が評価する、単位から第一行を経た同じ Ar[1] の添字。 -/
def firstRowOnePoint : 𝟙_ SSet.{u} ⟶ arNerve 1 :=
  firstRowOneUnitIso.inv ≫ firstRowInclusion 1

/-- 元の S₁ 比較は、同じ第一行の固定添字での実評価である。 -/
lemma sOneComparison_eq_unitEvaluation (C : SSet.{u}) :
    sOneComparison C = (gappedSubcomplex 1 C).ι ≫ (pre firstRowOnePoint).app C ≫
      (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app C := by
  change ((gappedSubcomplex 1 C).ι ≫ (pre (firstRowInclusion 1)).app C) ≫
    ((pre firstRowOneUnitIso.inv).app C ≫
      (MonoidalClosed.unitNatIso (C := SSet.{u})).inv.app C) = _
  rw [firstRowOnePoint, pre_map, NatTrans.comp_app]
  erw [Category.assoc, Category.assoc]

/-- 元の S₁ 比較は、全完全関手族の実作用と厳密に可換する。 -/
lemma sOneComparison_family_action (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    (sOneComparison C.obj ▷ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u})) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι = sExactFamilyAction 1 C D ≫ sOneComparison D.obj := by
  rw [sOneComparison_eq_unitEvaluation, sOneComparison_eq_unitEvaluation]
  erw [← Category.assoc (sExactFamilyAction 1 C D), sExactFamilyAction_inclusion,
    Category.assoc]
  exact closedEvaluationFamily_action firstRowOnePoint (gappedSubcomplex 1 C.obj).ι
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι

end SerrePositivity.KST.SConstruction
