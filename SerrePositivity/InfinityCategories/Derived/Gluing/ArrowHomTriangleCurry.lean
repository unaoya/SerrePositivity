module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTrianglePair

/-! 同じ二つの合成三角形を貼り、元の矢印圏の全区間 Hom へ厳密に戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {T X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⟶ X}

def dgGluingArrowHomTriangleSquare (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ T ⟶ X :=
  parameterizedSquareLift a.first a.second a.diagonal

lemma dgGluingArrowHomTriangleSquare_zero (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    (prismEndpoint 0 Δ[1] ▷ T) ≫ dgGluingArrowHomTriangleSquare a = fst Δ[1] T ≫ F := by
  rw [← triangleSquare_upper_left, comp_whiskerRight, Category.assoc,
    dgGluingArrowHomTriangleSquare, parameterizedSquareLift_zero]
  exact a.source

lemma dgGluingArrowHomTriangleSquare_one (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    (prismEndpoint 1 Δ[1] ▷ T) ≫ dgGluingArrowHomTriangleSquare a = fst Δ[1] T ≫ G := by
  rw [← triangleSquare_lower_right, comp_whiskerRight, Category.assoc,
    dgGluingArrowHomTriangleSquare, parameterizedSquareLift_one]
  exact a.target

def dgGluingArrowHomIntervalOfTriangles (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G) :=
  intervalFunctorHomPrismCurry (dgGluingArrowHomTriangleSquare a)
    (dgGluingArrowHomTriangleSquare_zero a) (dgGluingArrowHomTriangleSquare_one a)

lemma dgGluingArrowHomIntervalOfTriangles_prism
    (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    intervalFunctorHomPrism (dgGluingArrowHomIntervalOfTriangles a) =
      dgGluingArrowHomTriangleSquare a :=
  intervalFunctorHomPrism_curry _ _ _

lemma dgGluingArrowHomTriangles_interval (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    dgGluingArrowHomTrianglePairOfInterval F G (dgGluingArrowHomIntervalOfTriangles a) = a := by
  apply DGGluingArrowHomTrianglePair.ext
  · change (squareTriangle 0 ▷ T) ≫ intervalFunctorHomPrism _ = _
    rw [dgGluingArrowHomIntervalOfTriangles_prism, dgGluingArrowHomTriangleSquare,
      parameterizedSquareLift_zero]
  · change (squareTriangle 1 ▷ T) ≫ intervalFunctorHomPrism _ = _
    rw [dgGluingArrowHomIntervalOfTriangles_prism, dgGluingArrowHomTriangleSquare,
      parameterizedSquareLift_one]

def dgGluingArrowHomTriangleEquiv :
    (T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) ≃
      DGGluingArrowHomTrianglePair (T := T) F G where
  toFun := dgGluingArrowHomTrianglePairOfInterval F G
  invFun := dgGluingArrowHomIntervalOfTriangles
  left_inv f := by
    apply dgGluingArrowHomTrianglePairOfInterval_injective F G
    exact dgGluingArrowHomTriangles_interval _
  right_inv := dgGluingArrowHomTriangles_interval

end SerrePositivity.InfinityCategories
