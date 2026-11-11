module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedResidualHammockSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EndpointColimitSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph

/-!
# 元の一段の切断の単体写像

概要：最初の切断の依存和の点を全単体作用素へ照合し、単体集合の射にする。
方針：同じ生成矢と実際の二つの余極限の標準射の自然性を使う。
規約：始域の全行・全列・全縦射と指定 prefix の実際の W-hammock を保持する。
使われ方：自由積分解の切断の語への自然性と反復。

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

lemma point_simplex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).map θ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W τ h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) hθ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTargetTransport.point_ext W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_simplex W τ h θ hθ).symm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.image_simplex
      (⊤ : MorphismProperty (WideSubcategory W.paths))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord_simplex W τ h θ hθ).symm rfl
      (congrArg (fun a : Quiver.Total C => (⟨a.left⟩ : WideSubcategory W.paths))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_simplex W τ h θ hθ).symm) θ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedSimplex W τ h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedSimplex W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) hθ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedSimplex_simplex W τ h θ hθ)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.image_simplex W.paths
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord_simplex W τ h θ hθ).symm
      (congrArg (fun a : Quiver.Total C => (show Paths C from a.right))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_simplex W τ h θ hθ).symm) rfl θ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) hθ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ hθ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualFunctor_simplex W τ h θ hθ)

def cutMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.simplicialSet W w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y where
  app _ := ↾fun τ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W τ.val τ.property
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    exact (point_simplex W τ.val τ.property θ _).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
