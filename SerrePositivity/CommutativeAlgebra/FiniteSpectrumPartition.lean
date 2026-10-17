module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 有限個の商のスペクトルによる分割と元の有限直積写像

被約環のスペクトルが有限個の商のスペクトルで互いに素に被覆されれば、
元の商写像の直積は同型である。既存の中国剰余定理を使う。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity

/-- 被約環のスペクトルの有限商分割は、元の写像の直積を全単射にする。 -/
theorem pi_ringHom_bijective_of_spectrum_partition
    {ι : Type u} [Finite ι] (R : Type v) [CommRing R] [IsReduced R]
    (A : ι → Type w) [∀ i, CommRing (A i)] (f : ∀ i, R →+* A i)
    (hf : ∀ i, Function.Surjective (f i))
    (hdisjoint : Pairwise (fun i j => Disjoint
      (Set.range (PrimeSpectrum.comap (f i))) (Set.range (PrimeSpectrum.comap (f j)))))
    (hcover : (⋃ i, Set.range (PrimeSpectrum.comap (f i))) = Set.univ) :
    Function.Bijective (RingHom.pi f) := by
  have hcop : Pairwise (fun i j => IsCoprime (RingHom.ker (f i)) (RingHom.ker (f j))) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    rw [PrimeSpectrum.zeroLocus_sup,
      ← range_comap_of_surjective _ _ (hf i), ← range_comap_of_surjective _ _ (hf j)]
    exact Set.disjoint_iff_inter_eq_empty.mp (hdisjoint hij)
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply IsReduced.eq_zero (a - b)
    rw [nilpotent_iff_mem_prime]
    intro I hI
    have hmem : (⟨I, hI⟩ : PrimeSpectrum R) ∈
        ⋃ i, Set.range (PrimeSpectrum.comap (f i)) := by rw [hcover]; trivial
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hmem
    have habi : f i a = f i b := congrFun hab i
    have hz : f i (a - b) = 0 := by
      rw [map_sub, habi, sub_self]
    have hmem' : a - b ∈ (PrimeSpectrum.comap (f i) q).asIdeal := by
      change f i (a - b) ∈ q.asIdeal
      rw [hz]
      exact q.asIdeal.zero_mem
    simpa only [hq] using hmem'
  · intro y
    let e (i : ι) := RingHom.quotientKerEquivOfSurjective (hf i)
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop (fun i => (e i).symm (y i))
    refine ⟨r, funext (fun i => ?_)⟩
    change f i r = y i
    have hh := congrArg (e i) (hr i)
    dsimp only [e] at hh
    simpa only [RingHom.quotientKerEquivOfSurjective_apply_mk,
      RingEquiv.apply_symm_apply] using hh

end SerrePositivity
