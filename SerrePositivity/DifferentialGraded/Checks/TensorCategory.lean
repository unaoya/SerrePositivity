module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Complexes.TensorInterchange

/-! # U11b2：Mathlib transportによるtensor積dg圏 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]
example : DGCategory A (DGTensorCategory A B C) := inferInstance
example (x y : DGTensorCategory A B C) :
    (x ⟶[Complex A] y) = (x.1 ⟶[Complex A] y.1) ⊗ (x.2 ⟶[Complex A] y.2) :=
  dgTensor_hom A B C x y

#print axioms complexPairMonoidal
#print axioms dgPairEnrichment
#print axioms DGTensorCategory
#print axioms dgTensorEnrichment
#print axioms dgTensor_hom
#print axioms dgTensor_identity
#print axioms dgTensor_composition

#print axioms tensorμ_eq_shuffle
#print axioms tensorμ_apply
