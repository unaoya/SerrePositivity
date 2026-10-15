module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sets.Closeds

/-! # Closed supports and inverse images on prime spectra -/
@[expose] public section
universe u
namespace SerrePositivity
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- イデアルの零点集合を閉集合として扱う。 -/
def supportZeroLocus (I : Ideal R) : TopologicalSpace.Closeds (PrimeSpectrum R) :=
  ⟨PrimeSpectrum.zeroLocus I, PrimeSpectrum.isClosed_zeroLocus (I : Set R)⟩

@[simp] lemma coe_supportZeroLocus (I : Ideal R) :
    (supportZeroLocus I : Set (PrimeSpectrum R)) = PrimeSpectrum.zeroLocus I := rfl

/-- 台の指定はイデアルの零点集合だけに依存する。 -/
lemma supportZeroLocus_eq {I J : Ideal R}
    (h : PrimeSpectrum.zeroLocus I = PrimeSpectrum.zeroLocus (J : Set R)) :
    supportZeroLocus I = supportZeroLocus J := SetLike.coe_injective h

/-- Pull back a closed support along the map of prime spectra. -/
def supportPullback (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    TopologicalSpace.Closeds (PrimeSpectrum S) :=
  ⟨(PrimeSpectrum.comap φ) ⁻¹' Z, Z.isClosed.preimage (PrimeSpectrum.continuous_comap φ)⟩

@[simp] lemma mem_supportPullback (φ : R →+* S)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (p : PrimeSpectrum S) :
    p ∈ supportPullback φ Z ↔ PrimeSpectrum.comap φ p ∈ Z := Iff.rfl

@[simp] lemma supportPullback_id (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    supportPullback (RingHom.id R) Z = Z := by
  ext p
  simp [supportPullback, PrimeSpectrum.comap_id]

@[simp] lemma supportPullback_comp (φ : R →+* S) (ψ : S →+* T)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    supportPullback ψ (supportPullback φ Z) = supportPullback (ψ.comp φ) Z := by
  ext p
  simp [supportPullback]

lemma supportPullback_mono (φ : R →+* S)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    supportPullback φ Z ≤ supportPullback φ W := by
  intro p hp
  exact h hp

@[simp] lemma supportPullback_zeroLocus (φ : R →+* S) (I : Ideal R) :
    supportPullback φ (supportZeroLocus I) = supportZeroLocus (I.map φ) := by
  ext p
  change I ≤ p.asIdeal.comap φ ↔ I.map φ ≤ p.asIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- Pullback of a support specified by a generating list. -/
lemma supportPullback_span (φ : R →+* S) {e : ℕ} (z : Fin e → R) :
    supportPullback φ (supportZeroLocus (Ideal.span (Set.range z))) =
      supportZeroLocus (Ideal.span (Set.range (φ ∘ z))) := by
  rw [supportPullback_zeroLocus, Ideal.map_span, ← Set.range_comp]

variable (φ : R →+* S)

/-- Pullback of an intersection lies in an intersection of larger target supports. -/
lemma supportPullback_inf_le {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V) :
    supportPullback φ (Y ⊓ Z) ≤ W ⊓ V := by
  intro p hp
  exact ⟨hY hp.1, hZ hp.2⟩

lemma supportZeroLocus_mul_left (s t : R) :
    supportZeroLocus (Ideal.span ({s} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s * t} : Set R)) := by
  intro p hp
  change Ideal.span ({s * t} : Set R) ≤ p.asIdeal
  apply Ideal.span_le.mpr
  intro a ha
  have ha' : a = s * t := Set.mem_singleton_iff.mp ha
  subst a
  exact p.asIdeal.mul_mem_right t (hp (Ideal.subset_span (Set.mem_singleton s)))

lemma supportZeroLocus_mul_right (s t : R) :
    supportZeroLocus (Ideal.span ({t} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s * t} : Set R)) := by
  simpa only [mul_comm] using supportZeroLocus_mul_left t s

/-- Vanishing of a power implies vanishing of its base, including the empty locus for n = 0. -/
lemma supportZeroLocus_pow_le (s : R) (n : ℕ) :
    supportZeroLocus (Ideal.span ({s ^ n} : Set R)) ≤
      supportZeroLocus (Ideal.span ({s} : Set R)) := by
  intro p hp
  change Ideal.span ({s} : Set R) ≤ p.asIdeal
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  exact p.isPrime.mem_of_pow_mem n (hp (Ideal.subset_span (Set.mem_singleton _)))

end SerrePositivity
