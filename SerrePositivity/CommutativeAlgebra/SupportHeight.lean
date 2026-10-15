module

public import SerrePositivity.CommutativeAlgebra.ClosedSupportGeometry
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Height bounds and the finite set of least-height support points -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R]

/-- Height bounds retain the extended-natural value of prime height. -/
def HeightAtLeast (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) : Prop :=
  ∀ p ∈ Z, (c : ℕ∞) ≤ p.asIdeal.height

def heightStratum (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) :
    Set (PrimeSpectrum R) := {p | p ∈ Z ∧ p.asIdeal.height = (c : ℕ∞)}

lemma HeightAtLeast.mono {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}
    (h : HeightAtLeast Z c) (hW : W ≤ Z) : HeightAtLeast W c :=
  fun p hp => h p (hW hp)

lemma heightAtLeast_zero (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    HeightAtLeast Z 0 := fun _ _ => bot_le

lemma HeightAtLeast.ideal_height {I : Ideal R} {c : ℕ}
    (h : HeightAtLeast (supportZeroLocus I) c) : (c : ℕ∞) ≤ I.height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun J hJ => ?_
  let p : PrimeSpectrum R := ⟨J, hJ.isPrime⟩
  exact h p hJ.le

lemma HeightAtLeast.mem_minimalPrimes {I : Ideal R} {c : ℕ}
    (h : HeightAtLeast (supportZeroLocus I) c) {p : PrimeSpectrum R}
    (hp : p ∈ heightStratum (supportZeroLocus I) c) : p.asIdeal ∈ I.minimalPrimes := by
  let : p.asIdeal.FiniteHeight := ⟨Or.inr (hp.2 ▸ ENat.natCast_ne_top c)⟩
  exact Ideal.mem_minimalPrimes_of_height_le hp.1 (hp.2.le.trans h.ideal_height)

lemma HeightAtLeast.finite_heightStratum [IsNoetherianRing R]
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ} (h : HeightAtLeast Z c) :
    (heightStratum Z c).Finite := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp Z.isClosed
  have hZ : Z = supportZeroLocus I := SetLike.coe_injective hI
  subst Z
  have hs : PrimeSpectrum.asIdeal '' heightStratum (supportZeroLocus I) c ⊆ I.minimalPrimes := by
    rintro _ ⟨p, hp, rfl⟩
    exact h.mem_minimalPrimes hp
  exact Set.Finite.of_finite_image ((I.finite_minimalPrimes_of_isNoetherianRing R).subset hs)
    (fun _ _ _ _ h => PrimeSpectrum.ext h)

lemma heightStratum_eq_of_le {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {c : ℕ} {p q : PrimeSpectrum R}
    (hp : p ∈ heightStratum Z c) (hq : q ∈ heightStratum Z c) (hpq : p ≤ q) : p = q := by
  let : p.asIdeal.FiniteHeight := ⟨Or.inr (hp.2 ▸ ENat.natCast_ne_top c)⟩
  apply PrimeSpectrum.ext
  exact Ideal.eq_of_le_of_height_le p.asIdeal hpq (hq.2.le.trans hp.2.symm.le)

/-- The multiplicative set avoiding every least-height support point. -/
def heightStratumComplement (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) :
    Submonoid R where
  carrier := {s | ∀ p ∈ heightStratum Z c, s ∉ p.asIdeal}
  one_mem' := fun p _ => p.asIdeal.primeCompl.one_mem
  mul_mem' hs ht := fun p hp => p.asIdeal.primeCompl.mul_mem (hs p hp) (ht p hp)

@[simp]
lemma mem_heightStratumComplement {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {c : ℕ} {s : R} :
    s ∈ heightStratumComplement Z c ↔ ∀ p ∈ heightStratum Z c, s ∉ p.asIdeal := Iff.rfl

lemma heightStratumComplement_le_primeCompl {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {c : ℕ} {p : PrimeSpectrum R} (hp : p ∈ heightStratum Z c) :
    heightStratumComplement Z c ≤ p.asIdeal.primeCompl := fun _ hs => hs p hp

/-- Avoiding all height-c support points raises the height bound of the cut. -/
lemma HeightAtLeast.cut_succ {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}
    (h : HeightAtLeast Z c) (s : R)
    (hs : ∀ p ∈ heightStratum Z c, s ∉ p.asIdeal) :
    HeightAtLeast (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))) (c + 1) := by
  intro p hp
  have hne : p.asIdeal.height ≠ (c : ℕ∞) := by
    intro he
    exact hs p ⟨hp.1, he⟩ (hp.2 (Ideal.subset_span (Set.mem_singleton s)))
  have ht : (c : ℕ∞) < p.asIdeal.height := lt_of_le_of_ne (h p hp.1) hne.symm
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ENat.add_one_le_iff (ENat.natCast_ne_top c)).mpr ht

lemma HeightAtLeast.cut_succ_of_mem_complement
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ} (h : HeightAtLeast Z c)
    {s : R} (hs : s ∈ heightStratumComplement Z c) :
    HeightAtLeast (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))) (c + 1) :=
  h.cut_succ s hs

lemma HeightAtLeast.succ_of_heightStratum_empty
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ} (h : HeightAtLeast Z c)
    (he : heightStratum Z c = ∅) : HeightAtLeast Z (c + 1) := by
  intro p hp
  have hne : p.asIdeal.height ≠ (c : ℕ∞) := by
    intro hc
    have hm : p ∈ heightStratum Z c := ⟨hp, hc⟩
    rw [he] at hm
    exact hm
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ENat.add_one_le_iff (ENat.natCast_ne_top c)).mpr (lt_of_le_of_ne (h p hp) hne.symm)

/-- Above a finite ring-dimension bound, a closed support must be empty. -/
lemma HeightAtLeast.eq_bot_of_dimension_bound
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {d : ℕ}
    (h : HeightAtLeast Z (d + 1)) (hd : ringKrullDim R ≤ d) : Z = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  have hb : (p.asIdeal.height : WithBot ℕ∞) ≤ d :=
    p.asIdeal.height_le_ringKrullDim_of_isPrime.trans hd
  have hc : (d + 1 : ℕ∞) ≤ (d : ℕ∞) :=
    (h p hp).trans (WithBot.coe_le_coe.mp hb)
  have hn : d + 1 ≤ d := by exact_mod_cast hc
  omega

end Adams
end SerrePositivity
