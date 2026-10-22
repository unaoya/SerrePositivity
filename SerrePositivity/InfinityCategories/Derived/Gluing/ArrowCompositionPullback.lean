module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleCurry
public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceDiagonalPullback

/-! 始辺固定と終辺固定の合成対応を、同じ対角 Hom の上で厳密に引き戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
variable {X : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

def dgGluingArrowCompositionPullback : SSet.{u} :=
  pullback (dgGluingFirstFixedCompositionDiagonal f d) (compositionCorrespondenceDiagonal a g)

attribute [local instance] dgGluingFirstFixedCompositionSpace_kanComplex
  compositionCorrespondence_kanComplex

lemma dgGluingArrowCompositionPullback_kanComplex [Quasicategory X] :
    KanComplex (dgGluingArrowCompositionPullback f g) := by
  let : Fibration (compositionCorrespondenceDiagonal a g) :=
    compositionCorrespondenceDiagonal_fibration a g
  let : Fibration (pullback.fst (dgGluingFirstFixedCompositionDiagonal f d)
      (compositionCorrespondenceDiagonal a g)) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).2
    intro A B i hi
    let : HasLiftingProperty i (compositionCorrespondenceDiagonal a g) :=
      (SSet.modelCategoryQuillen.fibration_iff _).1
        (compositionCorrespondenceDiagonal_fibration a g) i hi
    exact (IsPullback.of_hasPullback (dgGluingFirstFixedCompositionDiagonal f d)
      (compositionCorrespondenceDiagonal a g)).flip.hasLiftingProperty i
  exact isFibrant_of_fibration
    (pullback.fst (dgGluingFirstFixedCompositionDiagonal f d)
      (compositionCorrespondenceDiagonal a g))

def dgGluingArrowCompositionPullbackTriangles :
    DGGluingArrowHomTrianglePair (T := dgGluingArrowCompositionPullback f g)
      (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge) where
  first := (Δ[2] ◁ pullback.fst _ _) ≫ dgGluingFirstFixedCompositionEvaluation f d
  second := (Δ[2] ◁ pullback.snd _ _) ≫ compositionCorrespondenceEvaluation a g
  diagonal := by
    have h := congrArg intervalMappingUncurry
      (pullback.condition (f := dgGluingFirstFixedCompositionDiagonal f d)
        (g := compositionCorrespondenceDiagonal a g))
    rw [intervalMappingUncurry_precomp, dgGluingFirstFixedCompositionDiagonal_uncurry,
      intervalMappingUncurry_precomp, compositionCorrespondenceDiagonal_uncurry] at h
    exact h
  source := by
    change (Δ[1] ◁ pullback.fst _ _) ≫
      ((stdSimplex.δ (2 : Fin 3) ▷ dgGluingFirstFixedCompositionSpace f d) ≫
        dgGluingFirstFixedCompositionEvaluation f d) = _
    rw [dgGluingFirstFixedCompositionEvaluation_first]
    rfl
  target := by
    change (Δ[1] ◁ pullback.snd _ _) ≫
      ((stdSimplex.δ (0 : Fin 3) ▷ compositionCorrespondence a g) ≫
        compositionCorrespondenceEvaluation a g) = _
    rw [compositionCorrespondenceEvaluation_last]
    rfl

def dgGluingArrowCompositionPullbackToHom :
    dgGluingArrowCompositionPullback f g ⟶
      intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
        (functorVertex (SSet.yonedaEquiv.symm g.edge)) :=
  dgGluingArrowHomIntervalOfTriangles (dgGluingArrowCompositionPullbackTriangles f g)

lemma dgGluingArrowCompositionPullbackToHom_triangles :
    dgGluingArrowHomTrianglePairOfInterval _ _ (dgGluingArrowCompositionPullbackToHom f g) =
      dgGluingArrowCompositionPullbackTriangles f g :=
  dgGluingArrowHomTriangles_interval _

end SerrePositivity.InfinityCategories
