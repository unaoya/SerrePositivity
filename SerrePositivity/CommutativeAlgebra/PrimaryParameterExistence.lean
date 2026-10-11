module

public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Data.Set.List

/-! # 準素イデアル内のパラメータ系の存在

Noether 局所環の極大イデアルを根基とするイデアルには、環の次元に等しい個数の
元からなるパラメータ系が含まれる。Krull の高さ定理による生成数の選択を用い、
Hilbert–Samuel 理論・正則局所環の非混合性には依存しない。
-/

@[expose] public section

open IsLocalRing

namespace SerrePositivity

namespace PrimaryParameterExistence

/-- 有限 Krull 次元は自然数化した次元から復元できる。 -/
theorem natCast_dimToNat (R : Type*) [CommRing R] [FiniteRingKrullDim R] :
    (dimToNat (ringKrullDim R) : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have hdt : d ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := R)
    rw [← hd, h]
    rfl
  rw [← hd, dimToNat, WithBot.unbotD_coe, ← WithBot.coe_natCast, ENat.natCast_toNat hdt]

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- 極大イデアルを根基とするイデアルの高さは環の次元に等しい。 -/
theorem height_eq_dim_of_radical_eq_maximalIdeal (I : Ideal R)
    (hI : I.radical = maximalIdeal R) :
    (I.height : WithBot ℕ∞) = ringKrullDim R := by
  have hmin : I.minimalPrimes = (maximalIdeal R).minimalPrimes := by
    rw [← hI, Ideal.radical_minimalPrimes]
  rw [I.height_eq_inf_minimalPrimes, hmin,
    ← (maximalIdeal R).height_eq_inf_minimalPrimes]
  exact maximalIdeal_height_eq_ringKrullDim

/-- 環の次元と同じ高さをもつ proper ideal の根基は極大イデアルである。 -/
theorem radical_eq_maximalIdeal_of_height_eq_dim (J : Ideal R) (hJ : J ≠ ⊤)
    (hd : (J.height : WithBot ℕ∞) = ringKrullDim R) :
    J.radical = maximalIdeal R := by
  refine le_antisymm
    ((maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr (le_maximalIdeal hJ)) ?_
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun p ⟨hJp, hprime⟩ ↦ ?_
  let : p.IsPrime := hprime
  have hpdim : (p.height : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm p.height_le_ringKrullDim_of_isPrime
      (hd ▸ WithBot.coe_le_coe.mpr (Ideal.height_mono hJp))
  rw [Ideal.height_eq_ringKrullDim_iff.mp hpdim]

/-- 任意の極大イデアル準素イデアルの中から、次元個の元で生成された
極大イデアル準素イデアルを選べる。 -/
theorem exists_parameters_in_primary (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    ∃ z : Fin (dimToNat (ringKrullDim R)) → R,
      (∀ i, z i ∈ I) ∧ (Ideal.span (Set.range z)).radical = maximalIdeal R := by
  classical
  have hItop : I ≠ ⊤ := by
    intro h
    have : (⊤ : Ideal R) = maximalIdeal R := by
      rw [h, Ideal.radical_top] at hI
      exact hI
    exact (maximalIdeal.isMaximal R).ne_top this.symm
  obtain ⟨J, hJI, hJrank, hJheight⟩ := I.exists_spanRank_eq_and_height_eq hItop
  have hJtop : J ≠ ⊤ := by
    intro h
    exact hItop (top_le_iff.mp (h ▸ hJI))
  have hJdim : (J.height : WithBot ℕ∞) = ringKrullDim R := by
    rw [hJheight]
    exact height_eq_dim_of_radical_eq_maximalIdeal R I hI
  have hJprimary := radical_eq_maximalIdeal_of_height_eq_dim R J hJtop hJdim
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian J).exists_span_finset_card_eq_spanFinrank
  have hdim : J.spanFinrank = dimToNat (ringKrullDim R) := by
    have hh : (J.spanFinrank : WithBot ℕ∞) = ringKrullDim R := by
      rw [← hJdim, hJheight]
      exact_mod_cast (Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
        (IsNoetherian.noetherian J)).symm.trans hJrank
    exact_mod_cast hh.trans (natCast_dimToNat R).symm
  have hlen : s.toList.length = dimToNat (ringKrullDim R) := by
    simpa [hcard] using hdim
  let z : Fin s.toList.length → R := s.toList.get
  have hz : Ideal.span (Set.range z) = J := by simpa [z] using hspan
  rw [← hlen]
  refine ⟨z, fun i ↦ ?_, hz ▸ hJprimary⟩
  exact hJI (hz ▸ Ideal.subset_span (Set.mem_range_self i))

/-- 選んだ列は、定義どおり環のパラメータ系である。 -/
theorem exists_systemOfParameters_in_primary (I : Ideal R)
    (hI : I.radical = maximalIdeal R) :
    ∃ z : Fin (dimToNat (ringKrullDim R)) → R,
      (∀ i, z i ∈ I) ∧ IsSystemOfParameters R z := by
  obtain ⟨z, hz, hrad⟩ := exists_parameters_in_primary R I hI
  exact ⟨z, hz, (natCast_dimToNat R).symm, hrad⟩

end PrimaryParameterExistence

end SerrePositivity
