module
public import SerrePositivity.DifferentialGraded.Category.TensorInclusions

/-! # tensor積への因子包含の受入検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]
example (c : C) : DGFunctor A B (DGTensorCategory A B C) := dgTensorIncludeFirst A B C c
example (b : B) : DGFunctor A C (DGTensorCategory A B C) := dgTensorIncludeSecond A B C b
#print axioms DGFunctor.ofHomMaps
#print axioms DGFunctor.map_unitElement
#print axioms DGFunctor.map_forward
#print axioms dgTensor_unitElement
#print axioms dgTensorFirstHom
#print axioms dgTensorFirstHom_apply
#print axioms dgTensorSecondHom
#print axioms dgTensorSecondHom_apply
#print axioms dgTensorIncludeFirst
#print axioms dgTensorIncludeSecond

#print axioms dgTensor_forward_of_sum
