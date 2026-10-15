module
public import SerrePositivity.DifferentialGraded.Category.TensorComposition

/-! # 通常順と豊穣順で異なるtensor積の交差符号を検査する -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]
example {x y z : DGTensorCategory A B C}
    (f₁ : GradedHom A x.1 y.1 1) (f₂ : GradedHom A x.2 y.2 0)
    (g₁ : GradedHom A y.1 z.1 0) (g₂ : GradedHom A y.2 z.2 1) :
    compose A (dgTensorElement A g₁ g₂ rfl) (dgTensorElement A f₁ f₂ rfl) (by omega) =
      -dgTensorElement A (compose A g₁ f₁ rfl) (compose A g₂ f₂ rfl)
        (show (1 : ℤ) + 0 + (0 + 1) = 2 by omega) := by
  simpa using dgTensor_compose A (n := 2) f₁ f₂ g₁ g₂ (by omega)
#print axioms dgTensorElement_units_smul
#print axioms dgTensor_compose
