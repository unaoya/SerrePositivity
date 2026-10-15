module
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import SerrePositivity.HomologicalAlgebra.ProjectiveExtColimitExact
public import SerrePositivity.HomologicalAlgebra.InjectiveCoefficientDimensionShift
public import SerrePositivity.HomologicalAlgebra.KoszulDualCoefficientExact
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyZeroTorsion

/-! # Arbitrary finite Koszul sequences compute actual local cohomology

No regularity of the parameter sequence is required. Both coefficient models
are exact and positively acyclic on injectives; their canonical zero-degree
comparison extends by natural dimension shifting.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {e : ℕ} (z : Fin e → R)

/-- The actual projective-resolution colimit for coordinate-power quotients
computes Mathlib local cohomology naturally in all coefficients and degrees. -/
def projectiveExtPowerQuotientLocalCohomologyNatIso (i : ℕ) :
    projectiveExtColimitFunctor
        (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)) ⋙
      homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
        localCohomology (Ideal.span (Set.range z)) i :=
  projectiveExtColimitFunctorHomologyNatIso _ i ≪≫
    Functor.Final.colimitIso (opOp ℕ) (localCohomology.diagram (powerKoszulIdealDiagram z) i) ≪≫
      localCohomologyPowerKoszulIdealNatIso z i

/-- An arbitrary finite sequence in a Noetherian ring computes actual local
cohomology by its actual dual power-Koszul colimit, naturally in coefficients. -/
def generalKoszulLocalCohomologyComparison (i : ℕ) :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  injectiveCoefficientHomologyNatIso
    (koszulDualColimitFunctor z)
    (projectiveExtColimitFunctor (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)))
    (fun J hJ n hn => by
      have : Injective J := hJ
      exact koszulDualColimit_injective_positive_homology_isZero z J n hn)
    (fun J hJ n hn => by
      have : Injective J := hJ
      exact projectiveExtColimitFunctor_injective_positive_homology_isZero _ J n hn)
    (koszulDualColimitZeroLocalCohomologyNatIso z ≪≫
      (projectiveExtPowerQuotientLocalCohomologyNatIso z 0).symm) i ≪≫
    projectiveExtPowerQuotientLocalCohomologyNatIso z i

/-- The all-degree comparison preserves and reflects zero induced coefficient maps. -/
lemma generalKoszulLocalCohomologyComparison_map_eq_zero_iff
    (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    homologyMap ((koszulDualColimitFunctor z).map f) i = 0 ↔
      (localCohomology (Ideal.span (Set.range z)) i).map f = 0 := by
  let E := generalKoszulLocalCohomologyComparison z i
  have hn := E.hom.naturality f
  constructor
  · intro hf
    apply (cancel_epi (E.app M).hom).mp
    simpa only [Functor.comp_map, homologyFunctor_map, Iso.app_hom, hf,
      zero_comp, comp_zero] using hn.symm
  · intro hf
    apply (cancel_mono (E.app N).hom).mp
    simpa only [Functor.comp_map, homologyFunctor_map, Iso.app_hom, hf,
      zero_comp, comp_zero] using hn

end SerrePositivity
