module

public import SerrePositivity.CommutativeAlgebra.EtaleAwayBaseChange

/-! # KL entry point for the existing standard localization base change theorem -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct

/-- Preserve the KL entry point using the existing general base change theorem.
The source and target use their specified standard localization algebras. -/
theorem etaleAway_tensor_baseChange
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      letI := GenericEtale.awayAlgebra B (B ⊗[R] A) (algebraMap R B g)
      Algebra.Etale (Localization.Away (algebraMap R B g))
        (Localization.Away (algebraMap B (B ⊗[R] A) (algebraMap R B g))) :=
  GenericEtale.etale_away_baseChange R B A g

end SerrePositivity
