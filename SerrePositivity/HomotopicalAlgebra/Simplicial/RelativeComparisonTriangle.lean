module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling

/-! # A relative triangle retains all three previously selected comparison edges -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeComparisonTriangle
variable {E B A X : SSet.{v}} {f g h : X ⟶ E}
  (F : SSet.Homotopy f g) (G : SSet.Homotopy g h) (H : SSet.Homotopy f h)

def faces : Fin 3 → (X ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ E) :=
  ![G.h, H.h, F.h]

lemma compatible : BoundaryTensorGluing.Compatible (faces F G H) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> simp at hjk
  · change X ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ G.h =
      X ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ H.h
    rw [HomotopyEndpointComparison.face_one, HomotopyEndpointComparison.face_one]
  · change X ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ G.h =
      X ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ F.h
    rw [HomotopyEndpointComparison.face_zero, HomotopyEndpointComparison.face_one]
  · change X ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ H.h =
      X ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ F.h
    rw [HomotopyEndpointComparison.face_zero, HomotopyEndpointComparison.face_zero]

variable (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (i : A ⟶ X) [Mono i] (a : A ⟶ E) (b : X ⟶ B) (hab : a ≫ p = i ≫ b)
  (hF : F.h ≫ p = fst X _ ≫ b) (hG : G.h ≫ p = fst X _ ≫ b)
  (hH : H.h ≫ p = fst X _ ≫ b)
  (rF : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ F.h = fst A _ ≫ a)
  (rG : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ G.h = fst A _ ≫ a)
  (rH : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h = fst A _ ≫ a)

def triangle : X ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ E :=
  RelativeBoundaryFilling.filler p hp i a b hab (faces F G H) (compatible F G H)
    (by
      intro k
      fin_cases k
      · exact hG
      · exact hH
      · exact hF)
    (by
      intro k
      fin_cases k
      · exact rG
      · exact rH
      · exact rF)

lemma triangle_face (k : Fin 3) : X ◁ SSet.stdSimplex.δ k ≫
    triangle F G H p hp i a b hab hF hG hH rF rG rH = faces F G H k :=
  RelativeBoundaryFilling.filler_face _ _ _ _ _ _ _ _ _ _ k

lemma triangle_base : triangle F G H p hp i a b hab hF hG hH rF rG rH ≫ p =
    fst X _ ≫ b := RelativeBoundaryFilling.filler_base _ _ _ _ _ _ _ _ _ _

lemma triangle_relative : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
    triangle F G H p hp i a b hab hF hG hH rF rG rH = fst A _ ≫ a :=
  RelativeBoundaryFilling.filler_relative _ _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.RelativeComparisonTriangle
