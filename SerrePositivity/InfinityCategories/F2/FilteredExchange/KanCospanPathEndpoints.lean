module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPullbackHomotopyPoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanSpecifiedHomotopy

/-!
概要：元の二入力と Kan 置換後の二入力の間で、指定 path の端点表示を移す。
方針：単位の自然性で三座標を揃え、指定全境界正方形を引き戻しへ持ち上げる。
規約：元の二入力の円柱を単位で写した全円柱を保持する。
使われ方：有限 path 模型の同時輸送から標的引き戻し内の実際のホモトピーへ進む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の入力からの指定 Kan path を、置換後の cospan の端点表示へ移す。
方針：単位の自然性で両端だけを書き換え、全円柱を保持する。
規約：h は H.h そのもの。使われ方：元の指定 path の引き戻しへの持ち上げ。 -/
def kanCospanUnitPath {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X)
    (u : K ⟶ E) (v : K ⟶ D)
    (H : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app X)
      (v ≫ g ≫ continuousKanReplacementUnit.app X)) :
    SSet.Homotopy ((u ≫ continuousKanReplacementUnit.app E) ≫ continuousKanReplacement.map f)
      ((v ≫ continuousKanReplacementUnit.app D) ≫ continuousKanReplacement.map g) where
  h := H.h
  h₀ := by
    change SSet.ι₀ ≫ H.h = (u ≫ continuousKanReplacementUnit.app E) ≫
      continuousKanReplacement.map f
    rw [H.h₀]
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun r ↦ u ≫ r) (continuousKanReplacementUnit.naturality f)
  h₁ := by
    change SSet.ι₁ ≫ H.h = (v ≫ continuousKanReplacementUnit.app D) ≫
      continuousKanReplacement.map g
    rw [H.h₁]
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun r ↦ v ≫ r) (continuousKanReplacementUnit.naturality g)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：置換後の二入力の指定 path を、元の入力の像の間の path として読む。
方針：単位の自然性で端点だけを戻す。
規約：h は H.h そのもの。使われ方：有限模型の二段の比較円柱の接続。 -/
def kanCospanRawPath {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X)
    (u : K ⟶ E) (v : K ⟶ D)
    (H : SSet.Homotopy ((u ≫ continuousKanReplacementUnit.app E) ≫ continuousKanReplacement.map f)
      ((v ≫ continuousKanReplacementUnit.app D) ≫ continuousKanReplacement.map g)) :
    SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app X)
      (v ≫ g ≫ continuousKanReplacementUnit.app X) where
  h := H.h
  h₀ := by
    change SSet.ι₀ ≫ H.h = u ≫ f ≫ continuousKanReplacementUnit.app X
    rw [H.h₀]
    simpa only [Functor.id_map, Category.assoc] using
      (congrArg (fun r ↦ u ≫ r) (continuousKanReplacementUnit.naturality f)).symm
  h₁ := by
    change SSet.ι₁ ≫ H.h = v ≫ g ≫ continuousKanReplacementUnit.app X
    rw [H.h₁]
    simpa only [Functor.id_map, Category.assoc] using
      (congrArg (fun r ↦ v ≫ r) (continuousKanReplacementUnit.naturality g)).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.F2
