module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureTensorRight

/-! # ε消去と右tensorの受入監査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A]

example (K P Q : Complex A) :
    (Cochain.ofHom ((α_ K (epsilonComplex A ⊗ P) Q).hom ≫
      K ◁ (α_ (epsilonComplex A) P Q).hom)).comp
        (eraseMiddle A K (P ⊗ Q)) (zero_add 1) =
    ((tensorRightHom Q (K ⊗ (epsilonComplex A ⊗ P)) (K ⊗ P)).f 1
      (eraseMiddle A K P)).comp (Cochain.ofHom (α_ K P Q).hom) (add_zero 1) :=
  eraseMiddle_tensorRight A K P Q

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseHead_tensorRight
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_tensorRight
