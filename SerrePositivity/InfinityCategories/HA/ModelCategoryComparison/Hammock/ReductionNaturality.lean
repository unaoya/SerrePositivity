module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.EraseSimplexNaturality

/-!
# 元の基本縮約の全単体的作用素での保存

概要：二つの基本縮約と有限回の縮約は、元の全 face・degeneracy で保存される。
方針：元の語の遷移の自然性と、元の恒等列の削除の自然性を使う。
規約：作用素の後にも、元の同じ縮約の対象と全射列を使う。
使われ方：縮約済みの代表の全作用素を合流性で定義する工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} {n m : SimplexCategoryᵒᵖ}

lemma map {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n} (h : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n r s) (α : n ⟶ m) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y m (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α r) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α s) := by
  cases h with
  | merge d p hp τ =>
    have he : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app m
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨_, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).map α τ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p) X Y).map α
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ) :=
      NatTrans.naturality_apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)) α τ
    have hh := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.merge (W := W) (X := X) (Y := Y) (n := m) d p hp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨_, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).map α τ)
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map]
    rw [← he]
    exact hh
  | erase j τ hτ =>
    have hh := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.erase (W := W) (X := X) (Y := Y) (n := m) j
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W _ X Y).map α τ) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.identityColumn_map W X Y j τ hτ α)
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map]
    rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex_map W X Y j τ hτ α]
    exact hh

lemma chain_map {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (h : Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r s) (α : n ⟶ m) :
    Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y m)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α r) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α s) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.map hs α)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction
