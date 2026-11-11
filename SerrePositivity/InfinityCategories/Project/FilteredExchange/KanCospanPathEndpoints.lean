module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の入力からの指定 Kan path を、置換後の cospan の端点表示へ移す。
方針：単位の自然性で両端だけを書き換え、全円柱を保持する。
規約：h は H.h そのもの。使われ方：元の指定 path の引き戻しへの持ち上げ。 -/
def kanCospanUnitPath {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X)
    (u : K ⟶ E) (v : K ⟶ D)
    (H : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)) :
    SSet.Homotopy ((u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      ((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) where
  h := H.h
  h₀ := by
    change SSet.ι₀ ≫ H.h = (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f
    rw [H.h₀]
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun r ↦ u ≫ r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f)
  h₁ := by
    change SSet.ι₁ ≫ H.h = (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g
    rw [H.h₁]
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun r ↦ v ≫ r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality g)
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
    (H : SSet.Homotopy ((u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      ((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g)) :
    SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) where
  h := H.h
  h₀ := by
    change SSet.ι₀ ≫ H.h = u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
    rw [H.h₀]
    simpa only [Functor.id_map, Category.assoc] using
      (congrArg (fun r ↦ u ≫ r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f)).symm
  h₁ := by
    change SSet.ι₁ ≫ H.h = v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
    rw [H.h₁]
    simpa only [Functor.id_map, Category.assoc] using
      (congrArg (fun r ↦ v ≫ r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality g)).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
