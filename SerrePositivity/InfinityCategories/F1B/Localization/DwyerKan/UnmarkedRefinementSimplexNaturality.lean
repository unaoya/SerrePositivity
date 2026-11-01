module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachedDiagramsSimplex
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedRefinementSimplex

/-!
# 元の refined 単体と全単体作用素の厳密な整合

概要：全 refined 図式の再添字を、元の nerve の同じ単体作用素へ移す。
方針：元の固定端点関手の厳密な等式を用いる。
規約：面・退化を含む全作用素と同じ圧縮射を保持する。
使われ方：元の hammock への貼り戻しの単体的整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma refinementMap_simplex :
    refinementMap W ((graph W.paths w X Y).map θ τ) i hθ = refinementMap W τ i h := rfl

lemma refinedSimplex_simplex :
    (graph W.paths (refinedWord w i) X Y).map θ (refinedSimplex W τ i h) =
      refinedSimplex W ((graph W.paths w X Y).map θ τ) i hθ :=
  (refinedFunctor_simplex W τ i h θ hθ).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
