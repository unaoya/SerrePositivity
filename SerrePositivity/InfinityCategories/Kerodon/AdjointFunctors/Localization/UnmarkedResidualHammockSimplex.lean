module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedPrefixHammockSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorColumns

/-!
# 選択した残りの hammock と全単体作用素

概要：最初の非指定列の残りの固定端点関手を、元の再添字へ照合する。
方針：選択位置・生成矢・全図式の既存の異種等式を結合する。
規約：端点の表示を含む全行・全縦射を保持する。
使われ方：依存和の切断射の単体的自然性。

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
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ []) (θ : n ⟶ m)
  (hθ : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) j ≠ [])

lemma residualWord_simplex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) hθ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) :=
  congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.index_simplex W τ h θ hθ)

lemma residualFunctor_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) hθ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ hθ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_heq (residualWord_simplex W τ h θ hθ)
    (congrArg (fun a : Quiver.Total C => (show Paths C from a.right))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_simplex W τ h θ hθ)) rfl _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_simplex W τ h θ hθ)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
