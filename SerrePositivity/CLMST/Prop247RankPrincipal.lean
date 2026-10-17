module

public import SerrePositivity.CLMST.Prop247RankImages

/-! # Prop 2.4.7：元の rank 開集合の主開表示

D(g) の開閉 rank 部分を R[1/g] の冪等元で表し、元の環の分子へ戻す。
g の正則性・非零性や rank の正値性は不要である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST

/-- 各実 rank 部分は g の倍数による主開集合である。空の部分も含む。 -/
theorem prop247_rankOpen_exists_basicOpen
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    ∃ a : R, prop247_rankOpen R S g hetale n = PrimeSpectrum.basicOpen (g * a) := by
  let H := prop247_awaySpectrumHomeomorph R g
  have hc : IsClopen {y : PrimeSpectrum (Localization.Away g) |
      prop247_awayRank R S g (H y) = n} :=
    ((prop247_awayRank_isLocallyConstant R S g hetale).isClopen_fiber n).preimage
      H.continuous
  obtain ⟨e, _he, he⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hc
  let v := IsLocalization.Away.sec g e
  have hv : algebraMap R (Localization.Away g) (g * v.1) =
      (algebraMap R (Localization.Away g) g) ^ (v.2 + 1) * e := by
    dsimp only [v]
    rw [map_mul, ← IsLocalization.Away.sec_spec g e, map_pow, pow_succ]
    ac_rfl
  have hm (y : PrimeSpectrum (Localization.Away g)) :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) y ∈
        PrimeSpectrum.basicOpen (g * v.1) ↔ y ∈ PrimeSpectrum.basicOpen e := by
    change algebraMap R (Localization.Away g) (g * v.1) ∉ y.asIdeal ↔ e ∉ y.asIdeal
    rw [hv]
    exact not_congr (y.asIdeal.unit_mul_mem_iff_mem
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow (v.2 + 1)))
  have hr (y : PrimeSpectrum (Localization.Away g)) :
      prop247_awayRank R S g (H y) = n ↔ y ∈ PrimeSpectrum.basicOpen e :=
    Set.ext_iff.mp he y
  refine ⟨v.1, ?_⟩
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ Subtype.val '' {z | prop247_awayRank R S g z = n} ↔
    x ∈ PrimeSpectrum.basicOpen (g * v.1)
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := (hm (H.symm z)).mpr ((hr (H.symm z)).mp (by simpa using hz))
    simpa only [← prop247_awaySpectrumHomeomorph_apply, H, Homeomorph.apply_symm_apply] using hz'
  · intro hx
    let z : PrimeSpectrum.basicOpen g :=
      ⟨x, PrimeSpectrum.basicOpen_mul_le_left g v.1 hx⟩
    refine ⟨z, ?_, rfl⟩
    have hx' : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) (H.symm z) ∈
        PrimeSpectrum.basicOpen (g * v.1) := by
      simpa only [← prop247_awaySpectrumHomeomorph_apply, H, Homeomorph.apply_symm_apply]
        using hx
    have hz' := (hr (H.symm z)).mpr ((hm (H.symm z)).mp hx')
    simpa only [Set.mem_ofPred_eq, Homeomorph.apply_symm_apply] using hz'

end SerrePositivity.CLMST
