module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordDiagonalAugmentation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram

/-!
# 元の全語の対角 graph 図式の proper 性

概要：元の全単体・標準射を保持して同じ比較を余極限へ渡す。
方針：元の点ごとの包含と交わり、同じ余極限余錐の普遍性を使う。
規約：全語の添字の filtered 性は仮定しない。
使われ方：DK5.7の元の左 hammock 比較の弱同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram
open _root_.CategoryTheory
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X) (X Y : C.category)
lemma wordDiagonalDiagram_proper : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalDiagram D C p hp X Y) where
  map_mono f hf := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphDiagram_map_app_injective (D.obj n).weakEquivalences f hf (p n X) (p n Y) n
  intersection_range f g hf hg := by
    ext n σ
    have he := congrArg (fun S : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (D.obj n).weakEquivalences _ (p n X) (p n Y)).Subcomplex =>
      σ ∈ S.obj n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_intersection_range (W := (D.obj n).weakEquivalences)
        (X := p n X) (Y := p n Y) f g hf hg)
    exact iff_of_eq he
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram
