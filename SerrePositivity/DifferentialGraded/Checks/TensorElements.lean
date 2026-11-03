module
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # tensor積の全次数合成公式の公理監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]
example {x y : DGTensorCategory A B C} (p q : ℤ)
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) : GradedHom A x y (p + q) :=
  dgTensorElement A f g rfl
#print axioms dgTensorElement
#print axioms dgTensor_forward
