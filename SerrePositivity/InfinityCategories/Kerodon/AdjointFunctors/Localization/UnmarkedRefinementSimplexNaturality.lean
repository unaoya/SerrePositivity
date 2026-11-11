module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedDiagramsSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRefinementSimplex

/-!
# 元の refined 単体と全単体作用素の厳密な整合

概要：全 refined 図式の再添字を、元の nerve の同じ単体作用素へ移す。
方針：元の固定端点関手の厳密な等式を用いる。
規約：面・退化を含む全作用素と同じ圧縮射を保持する。
使われ方：元の hammock への貼り戻しの単体的整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma refinementMap_simplex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinementMap W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinementMap W τ i h := rfl

lemma refinedSimplex_simplex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinedWord w i) X Y).map θ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinedSimplex W τ i h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinedSimplex W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinedFunctor_simplex W τ i h θ hθ).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
