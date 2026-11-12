module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteSimplexLift
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 元の固定語の graph の有限包による実際の余極限

概要：全体の同じ graph が有限部分集合図式の余極限となる。
方針：有限 grid の持ち上げで全射性、支持の和と射影の単射性で等式を回収する。
規約：元の全次数と全標準射を保持する。
使われ方：全語の余極限との交換と全被覆の可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory Limits
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)

def degreeCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a ⋙ (evaluation _ (Type (max u v))).obj n) :=
  ((evaluation _ (Type (max u v))).obj n).mapCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphCocone T X Y a)

lemma degree_surjective (n : SimplexCategoryᵒᵖ) (σ : (degreeCocone T X Y a n).pt) :
    ∃ S τ, σ = (degreeCocone T X Y a n).ι.app S τ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport σ, liftSimplex T X Y a n σ, (liftSimplex_projection T X Y a n σ).symm⟩

lemma degree_equal (n : SimplexCategoryᵒᵖ) (S R : Finset Q)
    (σ : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a).obj S).obj n)
    (τ : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a).obj R).obj n)
    (h : (degreeCocone T X Y a n).ι.app S σ = (degreeCocone T X Y a n).ι.app R τ) :
    ∃ (U : Finset Q) (f : S ⟶ U) (g : R ⟶ U),
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a).map f).app n σ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a).map g).app n τ := by
  refine ⟨S ∪ R, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projection_nerve_injective T X Y a (S ∪ R) n
  have h₁ := congrArg (fun k => k.app n σ)
    (graphMap_projection T X Y a (show S ⊆ S ∪ R from Finset.subset_union_left))
  have h₂ := congrArg (fun k => k.app n τ)
    (graphMap_projection T X Y a (show R ⊆ S ∪ R from Finset.subset_union_right))
  exact h₁.trans (h.trans h₂.symm)

def degree_isColimit (n : SimplexCategoryᵒᵖ) : IsColimit (degreeCocone T X Y a n) :=
  Types.FilteredColimit.isColimitOf _ _ (degree_surjective T X Y a n)
    (degree_equal T X Y a n)

def graphCocone_isColimit : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphCocone T X Y a) :=
  evaluationJointlyReflectsColimits _ (degree_isColimit T X Y a)

def graphColimitIso : colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (⊤ : MorphismProperty (Paths Q)) a ((Paths.of Q).obj X) ((Paths.of Q).obj Y) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (graphCocone_isColimit T X Y a)

lemma graphColimitIso_fac (S : Finset Q) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a) S ≫ (graphColimitIso T X Y a).hom =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (graphCocone_isColimit T X Y a) S

end SerrePositivity.EInfinity.Hammock.RootedFinite
