module
public import SerrePositivity.HomologicalAlgebra.InjectiveLinearYoneda
public import SerrePositivity.HomologicalAlgebra.ProjectiveExtNaturality
public import Mathlib.Algebra.Homology.SingleHomology

/-! # Positive acyclicity of projective-resolution duals on injective coefficients -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
variable {R : Type u} [CommRing R]

/-- Positive homology of any actual projective resolution vanishes. -/
lemma projectiveResolution_positive_homology_isZero {X : ModuleCat.{u} R}
    (P : ProjectiveResolution X) (i : ℕ) (hi : 0 < i) :
    IsZero (P.complex.homology i) := by
  apply IsZero.of_iso _ (isoOfQuasiIsoAt P.π i)
  exact isZero_single_obj_homology (.down ℕ) 0 X i (Nat.ne_of_gt hi)

/-- Dualizing a projective resolution into an injective coefficient module
has no positive cohomology, without any regular-sequence assumption. -/
lemma projectiveResolution_injective_dual_positive_homology_isZero
    {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) :
    IsZero (((chainLinearYonedaFunctor P.complex).obj J).homology i) := by
  apply IsZero.of_iso _ (injectiveChainLinearYonedaHomologyIso P.complex J i)
  exact ((linearYoneda R (ModuleCat.{u} R)).obj J).map_isZero
    (projectiveResolution_positive_homology_isZero P i hi).op

end SerrePositivity
