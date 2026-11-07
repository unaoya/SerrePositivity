module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
概要：被約 Noether アフィンスキームの稠密開に含まれる正則主開を取る。
方針：稠密開がすべての最小素点を含むことを示し、素イデアル回避を使う。
規約：正則元は非零因子の部分モノイドへの所属で表す。
使われ方：一般平坦性で得た開集合を、有限加群の平坦化で使う正則な主境界にする。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

private theorem minimalPrime_mem_of_dense_open {R : Type*} [CommRing R] [IsNoetherianRing R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) (hU : Dense U.carrier)
    (P : Ideal R) (hP : P ∈ minimalPrimes R) : (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ U := by
  classical
  let finitePrimes := minimalPrimes.finite_of_isNoetherianRing (R := R)
  let others := finitePrimes.toFinset.erase P
  let : P.IsPrime := hP.isPrime
  have hex (Q : others) : ∃ x : R, x ∈ (Q : Ideal R) ∧ x ∉ P := by
    have hQ : (Q : Ideal R) ∈ minimalPrimes R :=
      finitePrimes.mem_toFinset.mp (Finset.mem_of_mem_erase Q.property)
    by_contra! h
    have hle : (Q : Ideal R) ≤ P := fun _ hx => h _ hx
    exact (Finset.ne_of_mem_erase Q.property) (hle.antisymm (hP.2 hQ.1 hle))
  let x (Q : others) := (hex Q).choose
  let s := ∏ Q : others, x Q
  have hsP : s ∉ P := by
    intro hs
    obtain ⟨Q, _, hQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hs
    exact (hex Q).choose_spec.2 hQ
  let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  let V := PrimeSpectrum.basicOpen s
  obtain ⟨q, hqV, hqU⟩ := dense_iff_inter_open.mp hU V.carrier V.isOpen ⟨p, hsP⟩
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
    (bot_le : (⊥ : Ideal R) ≤ q.asIdeal)
  have heq : Q = P := by
    by_contra hn
    let i : others := ⟨Q, Finset.mem_erase.mpr ⟨hn, finitePrimes.mem_toFinset.mpr hQ⟩⟩
    have hmem : s ∈ Q := by
      change (∏ j : others, x j) ∈ Q
      rw [← Finset.prod_erase_mul _ x (Finset.mem_univ i)]
      exact Q.mul_mem_left _ (hex i).choose_spec.1
    exact hqV (hle hmem)
  have hpq : p ≤ q := (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (show P ≤ q.asIdeal from heq ▸ hle)
  exact U.isOpen.stableUnderGeneralization ((PrimeSpectrum.le_iff_specializes p q).mp hpq) hqU

/--
概要：被約 Noether 環のスペクトルの任意の稠密開は、非零因子の主開を含む。
方針：稠密開の補集合を定めるイデアルから、どの最小素イデアルにも属さない元を取る。
規約：環が零環の場合も含む。
使われ方：一般平坦開の中に、主境界の平坦化を適用できる開を選ぶ。
-/
theorem exists_nonZeroDivisor_basicOpen_le_of_dense
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) (hU : Dense U.carrier) :
    ∃ t : R, t ∈ nonZeroDivisors R ∧ PrimeSpectrum.basicOpen t ≤ U := by
  let I := PrimeSpectrum.vanishingIdeal (U.carrierᶜ)
  have hV : PrimeSpectrum.zeroLocus (I : Set R) = U.carrierᶜ := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact U.isOpen.isClosed_compl.closure_eq
  have hnot (P : Ideal R) (hP : P ∈ minimalPrimes R) : ¬ I ≤ P := by
    intro hp
    have hm : (⟨P, hP.isPrime⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (I : Set R) := hp
    rw [hV] at hm
    exact hm (minimalPrime_mem_of_dense_open U hU P hP)
  have havoid : ¬ (I : Set R) ⊆ ⋃ P ∈ minimalPrimes R, (P : Set R) := by
    intro h
    obtain ⟨P, hP, hp⟩ := (Ideal.subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing (R := R)) (f := id) ⊥ ⊥
      (fun P hP _ _ => hP.isPrime)).mp h
    exact hnot P hP hp
  obtain ⟨t, ht, hmin⟩ := Set.not_subset.mp havoid
  have htP (P : Ideal R) (hP : P ∈ minimalPrimes R) : t ∉ P := fun hp =>
    hmin (Set.mem_iUnion₂.mpr ⟨P, hP, hp⟩)
  refine ⟨t, mem_nonZeroDivisors_iff_left.mpr ?_, ?_⟩
  · intro y hy
    have hm : y ∈ sInf (minimalPrimes R) := Ideal.mem_sInf.mpr fun P hP => by
      exact (hP.isPrime.mem_or_mem (hy.symm ▸ P.zero_mem)).resolve_left (htP P hP)
    change y ∈ sInf (Ideal.minimalPrimes (⊥ : Ideal R)) at hm
    rw [Ideal.sInf_minimalPrimes] at hm
    change y ∈ nilradical R at hm
    rwa [nilradical_eq_bot_iff.mpr (inferInstance : IsReduced R), Ideal.mem_bot] at hm
  · intro p hp
    by_contra hn
    have hm : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := hV.symm ▸ hn
    exact hp (hm ht)

end SerrePositivity.AlgebraicGeometry
