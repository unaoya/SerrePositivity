module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleCurry

/-! 二合成三角形の厳密な表示は、任意の高次パラメーターの引き戻しと可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {S T X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⟶ X}

def dgGluingArrowHomTriangleReindex (k : S ⟶ T)
    (a : DGGluingArrowHomTrianglePair (T := T) F G) :
    DGGluingArrowHomTrianglePair (T := S) F G where
  first := (Δ[2] ◁ k) ≫ a.first
  second := (Δ[2] ◁ k) ≫ a.second
  diagonal := by
    change (Δ[1] ◁ k) ≫ ((stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a.first) =
      (Δ[1] ◁ k) ≫ ((stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a.second)
    rw [a.diagonal]
  source := by
    change (Δ[1] ◁ k) ≫ ((stdSimplex.δ (2 : Fin 3) ▷ T) ≫ a.first) = _
    rw [a.source]
    rfl
  target := by
    change (Δ[1] ◁ k) ≫ ((stdSimplex.δ (0 : Fin 3) ▷ T) ≫ a.second) = _
    rw [a.target]
    rfl

lemma dgGluingArrowHomPrism_precomp (k : S ⟶ T)
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    intervalFunctorHomPrism (k ≫ f) =
      ((Δ[1] ⊗ Δ[1]) ◁ k) ≫ intervalFunctorHomPrism f := by
  unfold intervalFunctorHomPrism
  rw [intervalMappingUncurry_precomp]
  rfl

lemma dgGluingArrowHomTriangles_naturality (k : S ⟶ T)
    (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G)) :
    dgGluingArrowHomTrianglePairOfInterval F G (k ≫ f) =
      dgGluingArrowHomTriangleReindex k (dgGluingArrowHomTrianglePairOfInterval F G f) := by
  apply DGGluingArrowHomTrianglePair.ext
  · change (squareTriangle 0 ▷ S) ≫ intervalFunctorHomPrism (k ≫ f) = _
    rw [dgGluingArrowHomPrism_precomp]
    rfl
  · change (squareTriangle 1 ▷ S) ≫ intervalFunctorHomPrism (k ≫ f) = _
    rw [dgGluingArrowHomPrism_precomp]
    rfl

end SerrePositivity.InfinityCategories
