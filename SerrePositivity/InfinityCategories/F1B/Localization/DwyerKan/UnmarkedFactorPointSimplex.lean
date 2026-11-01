module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFactorPoint
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedResidualHammockSimplex
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EndpointColimitSimplex
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedNonemptyGraph

/-!
# 元の一段の切断の単体写像

概要：最初の切断の依存和の点を全単体作用素へ照合し、単体集合の射にする。
方針：同じ生成矢と実際の二つの余極限の標準射の自然性を使う。
規約：始域の全行・全列・全縦射と指定 prefix の実際の W-hammock を保持する。
使われ方：自由積分解の切断の語への自然性と反復。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ []) (θ : n ⟶ m)
  (hθ : ∃ j, column W (((graph W.paths w X Y).map θ τ).obj 0) j ≠ [])

lemma point_simplex :
    (FactorTarget.space W X Y).map θ (point W τ h) =
      point W ((graph W.paths w X Y).map θ τ) hθ := by
  apply FactorTarget.point_ext W (AttachedPrefix.generator_simplex W τ h θ hθ).symm
  · exact EndpointChange.image_simplex
      (⊤ : MorphismProperty (WideSubcategory W.paths))
      (AttachedPrefix.prefixWord_simplex W τ h θ hθ).symm rfl
      (congrArg (fun a : Quiver.Total C => (⟨a.left⟩ : WideSubcategory W.paths))
        (AttachedPrefix.generator_simplex W τ h θ hθ).symm) θ
      (AttachedPrefix.markedSimplex W τ h)
      (AttachedPrefix.markedSimplex W ((graph W.paths w X Y).map θ τ) hθ)
      (AttachedPrefix.markedSimplex_simplex W τ h θ hθ)
  · exact EndpointChange.image_simplex W.paths
      (AttachedPrefix.residualWord_simplex W τ h θ hθ).symm
      (congrArg (fun a : Quiver.Total C => (show Paths C from a.right))
        (AttachedPrefix.generator_simplex W τ h θ hθ).symm) rfl θ
      (Attachments.residualFunctor W τ (AttachedPrefix.index W τ h)
        (AttachedPrefix.nonempty W τ h))
      (Attachments.residualFunctor W ((graph W.paths w X Y).map θ τ)
        (AttachedPrefix.index W ((graph W.paths w X Y).map θ τ) hθ)
        (AttachedPrefix.nonempty W _ hθ))
      (AttachedPrefix.residualFunctor_simplex W τ h θ hθ)

def cutMap (w : Word) (X Y : Paths C) :
    NonemptyGraph.simplicialSet W w X Y ⟶ FactorTarget.space W X Y where
  app _ := ↾fun τ => point W τ.val τ.property
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    exact (point_simplex W τ.val τ.property θ _).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
