module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # A surjective quotient commutes with localization at a pulled-back prime -/

@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity
variable {C : Type u} {D : Type v} [CommRing C] [CommRing D]
    (π : C →+* D) (hπ : Function.Surjective π)
    (B : Type w) [CommRing B] [Algebra C B]

/-- The quotient of a C-algebra by the extended kernel is a D-algebra. -/
@[instance_reducible]
def localizedSurjectiveQuotientAlgebra :
    Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
  ((algebraMap (C ⧸ RingHom.ker π) (B ⧸ (RingHom.ker π).map (algebraMap C B))).comp
    (π.quotientKerEquivOfSurjective hπ).symm.toRingHom).toAlgebra

lemma localizedSurjectiveQuotientAlgebra_commutes (x : C) :
    let : Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
      localizedSurjectiveQuotientAlgebra π hπ B
    algebraMap D (B ⧸ (RingHom.ker π).map (algebraMap C B)) (π x) =
      Ideal.Quotient.mk _ (algebraMap C B x) := by
  change algebraMap (C ⧸ RingHom.ker π) _
    ((π.quotientKerEquivOfSurjective hπ).symm (π x)) = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- The quotient of the localization localizes the target at the original prime. -/
lemma isLocalization_localizedSurjectiveQuotient (q : Ideal D) [q.IsPrime]
    [IsLocalization (q.comap π).primeCompl B] :
    let : Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
      localizedSurjectiveQuotientAlgebra π hπ B
    IsLocalization q.primeCompl (B ⧸ (RingHom.ker π).map (algebraMap C B)) := by
  let : Algebra D (B ⧸ (RingHom.ker π).map (algebraMap C B)) :=
    localizedSurjectiveQuotientAlgebra π hπ B
  have hl : IsLocalization ((q.comap π).primeCompl.map π)
      (B ⧸ (RingHom.ker π).map (algebraMap C B)) := by
    apply IsLocalization.of_surjective (q.comap π).primeCompl B π hπ
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    · ext x
      exact (localizedSurjectiveQuotientAlgebra_commutes π hπ B x).symm
    · rw [Ideal.mk_ker]
  rw [Ideal.map_primeCompl_comap_of_surjective π hπ q] at hl
  exact hl

end SerrePositivity
