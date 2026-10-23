module
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFunctorHomPrismCurry
public import SerrePositivity.InfinityCategories.F1.Diagrams.ParameterizedSquare
public import SerrePositivity.InfinityCategories.F1B.FunctorTriangleSquare

/-! 矢印圏の実区間 Hom を、共通対角を持つ二つの全パラメーター三角形へ分ける。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {T X : SSet.{u}} (F G : (Δ[1] : SSet.{u}) ⟶ X)

structure DGGluingArrowHomTrianglePair where
  first : (Δ[2] : SSet.{u}) ⊗ T ⟶ X
  second : (Δ[2] : SSet.{u}) ⊗ T ⟶ X
  diagonal : (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ first =
    (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ second
  source : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ first = fst Δ[1] T ≫ F
  target : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ second = fst Δ[1] T ≫ G

@[ext] lemma DGGluingArrowHomTrianglePair.ext
    {a b : DGGluingArrowHomTrianglePair (T := T) F G}
    (hfirst : a.first = b.first) (hsecond : a.second = b.second) : a = b := by
  cases a
  cases b
  cases hfirst
  cases hsecond
  rfl

def dgGluingArrowHomTrianglePairOfInterval
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    DGGluingArrowHomTrianglePair (T := T) F G where
  first := (squareTriangle 0 ▷ T) ≫ intervalFunctorHomPrism f
  second := (squareTriangle 1 ▷ T) ≫ intervalFunctorHomPrism f
  diagonal := by
    simp only [← Category.assoc, ← comp_whiskerRight, squareTriangle_diagonal]
  source := by
    rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_upper_left]
    exact intervalFunctorHomPrism_zero f
  target := by
    rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_lower_right]
    exact intervalFunctorHomPrism_one f

lemma dgGluingArrowHomTrianglePairOfInterval_injective :
    Function.Injective (dgGluingArrowHomTrianglePairOfInterval (T := T) F G) := by
  intro f g h
  apply intervalFunctorHomPrism_injective F G
  apply parameterizedSquare_hom_ext
  · exact congrArg DGGluingArrowHomTrianglePair.first h
  · exact congrArg DGGluingArrowHomTrianglePair.second h

end SerrePositivity.InfinityCategories
