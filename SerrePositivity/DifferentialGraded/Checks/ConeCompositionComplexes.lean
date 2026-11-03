module
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-! # 八面体用の既存複体比較の受入検査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CochainComplex SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {K L P : Complex A}

example (f : K ⟶ L) (g : L ⟶ P) :
    HomotopyEquiv (mappingCone g)
      (mappingCone (mappingCone.map f (f ≫ g) (𝟙 K) g (by simp))) :=
  complexConeCompHomotopyEquiv f g (f ≫ g) rfl _ rfl

#print axioms complexConeCompHomotopyEquiv
#print axioms complexConeComp_hom_cochain
#print axioms complexConeComp_inv_cochain
#print axioms complexConeComp_hom_inv
#print axioms complexConeComp_inv_hom_boundary
#print axioms complexConeComp_inr_inv
#print axioms complexConeComp_hom_connecting
