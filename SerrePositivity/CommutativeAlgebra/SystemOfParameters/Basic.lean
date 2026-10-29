module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # パラメータ系の定義と次元の基本補題

## 概要

- `dimToNat`：`WithBot ℕ∞` 値の次元を自然数に落とす。有限次元なら元に戻る
  （`natCast_dimToNat_ringKrullDim`）。
- `IsSystemOfParameters D z`：`z = (z_1, …, z_h)` が局所環 `D` のパラメータ系であること。
  すなわち `h = dim D` で、`(z)` が `m_D` 準素（根基が `m_D`）。自己同型と成分の冪で保たれる。
- 局所環のイデアル `J ≠ ⊤` について、`√J = m` は `dim R/J ≤ 0` とも
  （`radical_eq_maximalIdeal_iff_ringKrullDim_quotient_le_zero`）、`ht J = dim R` とも
  （`radical_eq_maximalIdeal_iff_height_eq_ringKrullDim`、Noether のとき）同値。
- 素イデアル `p` について `ht p + dim R/p ≤ dim R`（`height_add_ringKrullDim_quotient_le`）と、
  `dim R/p` は `p` の余高さ（`ringKrullDim_quotient_eq_coheight`）。

## 方針

`√J = m` と `dim R/J ≤ 0` の同値は、`R/J` の素イデアルが `m` だけになることによる。
高さとの同値は、`J` の極小素イデアルと `m` の極小素イデアルの比較と、高さが次元に等しい素イデアルは
`m` であること（`Ideal.height_eq_ringKrullDim_iff`）による。

## 規約

パラメータ系の個数は添字の型 `Fin h` で持つ。次元の等式は `WithBot ℕ∞` で述べる。

## 使われ方

パラメータ系の存在（`SystemOfParameters/Existence`）、生成元の取り替え（`Generators`）、
有限な拡大（`Finite`）、素イデアル回避（`Avoidance`）、論文 §2（Lemma 2.2、Theorem 2.5）、
正則局所環と Hilbert–Samuel の理論。Mathlib への提出候補（mathlib-upstream の G10）。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing PrimeSpectrum

namespace SerrePositivity

section Defs

/-- `WithBot ℕ∞` 値の次元（`ringKrullDim`、`Module.supportDim`）を自然数に落とす。`⊥`（零環・
零加群）と `⊤`（無限次元）は `0` になる。有限次元の場合だけが意味をもつ。 -/
noncomputable def dimToNat (d : WithBot ℕ∞) : ℕ := (d.unbotD 0).toNat

variable (D : Type u) [CommRing D]

/-- `z : Fin h → D` が局所環 `D` のパラメータ系であること：`h = dim D`（Krull 次元）かつ `(z)` が
`m_D` 準素（`√(z) = m_D`）。Lemma 2.2 の正規化基底の条件（`A` の正則パラメータ系が `D` の
パラメータ系になる、`Paper/Section2/Lemma2_2.lean`）に使う。 -/
def IsSystemOfParameters [IsLocalRing D] {h : ℕ} (z : Fin h → D) : Prop :=
  ringKrullDim D = h ∧ (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D

/-- 局所環の自己同型はパラメータ系を保つ。長さ代数上の群作用は必要ない。 -/
theorem IsSystemOfParameters.map_aut [IsLocalRing D] {h : ℕ} {z : Fin h → D}
    (hz : IsSystemOfParameters D z) (σ : D ≃+* D) :
    IsSystemOfParameters D (σ ∘ z) := by
  refine ⟨hz.1, ?_⟩
  rw [Set.range_comp, ← Ideal.map_span]
  change (Ideal.map σ.toRingHom _).radical = _
  rw [← Ideal.map_radical_of_surjective σ.surjective
    (by
      intro a ha
      have : a = 0 := σ.injective (by simpa using ha)
      simpa only [this] using (Ideal.span (Set.range z)).zero_mem), hz.2]
  exact IsLocalRing.map_ringEquiv_maximalIdeal σ

/-- パラメータ系の各成分を正の冪にしてもパラメータ系である。
生成イデアルの根基が変わらないことを直接示す。 -/
theorem IsSystemOfParameters.pow [IsLocalRing D] {h : ℕ} {z : Fin h → D}
    (hz : IsSystemOfParameters D z) (v : ℕ) (hv : 0 < v) :
    IsSystemOfParameters D (fun i ↦ z i ^ v) := by
  refine ⟨hz.1, le_antisymm ?_ ?_⟩
  · rw [← hz.2]
    apply Ideal.radical_mono
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) v hv
  · rw [← hz.2]
    have hle : Ideal.span (Set.range z) ≤
        (Ideal.span (Set.range fun i ↦ z i ^ v)).radical := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_radical_iff.mpr ⟨v, Ideal.subset_span (Set.mem_range_self i)⟩
    simpa only [Ideal.radical_idem] using Ideal.radical_mono hle

/-- 有限次元の環では、自然数化した次元から元の Krull 次元が復元できる。 -/
theorem natCast_dimToNat_ringKrullDim (S : Type*) [CommRing S] [FiniteRingKrullDim S] :
    (dimToNat (ringKrullDim S) : WithBot ℕ∞) = ringKrullDim S := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := S))
  have hdt : d ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := S)
    rw [← hd, h]
    rfl
  rw [← hd, dimToNat, WithBot.unbotD_coe, ← WithBot.coe_natCast, ENat.natCast_toNat hdt]

end Defs

section Radical

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- 極大イデアルを根基とするイデアルの商は零次元以下。 -/
theorem ringKrullDim_quotient_le_zero_of_radical_eq_maximalIdeal (I : Ideal R)
    (hI : I.radical = maximalIdeal R) : ringKrullDim (R ⧸ I) ≤ 0 := by
  rw [ringKrullDim_quotient]
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun q q' _ ↦ ?_
  have hm : maximalIdeal R ≤ q.1.asIdeal := by
    rw [← hI, ← q.1.isPrime.radical]
    exact Ideal.radical_mono q.2
  exact (le_maximalIdeal q'.1.isPrime.ne_top).trans hm

/-- 局所環の proper なイデアル `J` について、`√J = m` と `dim R/J ≤ 0` は同値。 -/
theorem radical_eq_maximalIdeal_iff_ringKrullDim_quotient_le_zero {J : Ideal R} (hJ : J ≠ ⊤) :
    J.radical = maximalIdeal R ↔ ringKrullDim (R ⧸ J) ≤ 0 := by
  refine ⟨ringKrullDim_quotient_le_zero_of_radical_eq_maximalIdeal J, fun hdim ↦ ?_⟩
  refine le_antisymm ((Ideal.IsPrime.radical_le_iff (maximalIdeal.isMaximal R).isPrime).mpr
    (le_maximalIdeal hJ)) ?_
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun p ⟨hJp, hp⟩ ↦ ?_
  rw [ringKrullDim_quotient] at hdim
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hdim
    ⟨⟨p, hp⟩, by simpa [mem_zeroLocus] using hJp⟩
  have hm : (⟨⟨maximalIdeal R, inferInstance⟩, by
      simpa [mem_zeroLocus] using le_maximalIdeal hJ⟩ : zeroLocus (R := R) J) ≥
      ⟨⟨p, hp⟩, by simpa [mem_zeroLocus] using hJp⟩ :=
    show p ≤ maximalIdeal R from le_maximalIdeal hp.ne_top
  exact hmax hm

/-- 根基が極大イデアルである左因子に、極大イデアル内のイデアルを加えても根基は変わらない。 -/
theorem radical_sup_eq_maximalIdeal (I J : Ideal R)
    (hI : I.radical = maximalIdeal R) (hJ : J ≤ maximalIdeal R) :
    (I ⊔ J).radical = maximalIdeal R := by
  refine le_antisymm ?_ ?_
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr
      (sup_le (hI ▸ I.le_radical) hJ)
  · rw [← hI]
    exact Ideal.radical_mono le_sup_left

/-- 極大イデアルを根基とするイデアルの高さは環の次元に等しい。 -/
theorem height_eq_ringKrullDim_of_radical_eq_maximalIdeal (I : Ideal R)
    (hI : I.radical = maximalIdeal R) :
    (I.height : WithBot ℕ∞) = ringKrullDim R := by
  have hmin : I.minimalPrimes = (maximalIdeal R).minimalPrimes := by
    rw [← hI, Ideal.radical_minimalPrimes]
  rw [I.height_eq_inf_minimalPrimes, hmin,
    ← (maximalIdeal R).height_eq_inf_minimalPrimes]
  exact maximalIdeal_height_eq_ringKrullDim

/-- Noether 局所環の proper なイデアル `J` について、`√J = m` と `ht J = dim R` は同値。 -/
theorem radical_eq_maximalIdeal_iff_height_eq_ringKrullDim [IsNoetherianRing R]
    {J : Ideal R} (hJ : J ≠ ⊤) :
    J.radical = maximalIdeal R ↔ (J.height : WithBot ℕ∞) = ringKrullDim R := by
  refine ⟨height_eq_ringKrullDim_of_radical_eq_maximalIdeal J, fun hd ↦ ?_⟩
  refine le_antisymm
    ((maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr (le_maximalIdeal hJ)) ?_
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun p ⟨hJp, hprime⟩ ↦ ?_
  let : p.IsPrime := hprime
  have hpdim : (p.height : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm p.height_le_ringKrullDim_of_isPrime
      (hd ▸ WithBot.coe_le_coe.mpr (Ideal.height_mono hJp))
  rw [Ideal.height_eq_ringKrullDim_iff.mp hpdim]

end Radical

section Height

variable {R : Type u} [CommRing R]

/-- 素イデアルによる商の次元は、その素イデアルの順序の余高さに等しい。 -/
lemma ringKrullDim_quotient_eq_coheight (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  rw [ringKrullDim,
    Order.krullDim_eq_of_orderIso p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus]
  have hz : PrimeSpectrum.zeroLocus (p.asIdeal : Set R) = Set.Ici p := by
    ext q
    rfl
  rw [hz, ← Order.coheight_eq_krullDim_Ici]

/-- 素イデアルの高さと商の次元の和は環の次元以下（下と上の鎖をつなぐ）。 -/
lemma height_add_ringKrullDim_quotient_le (p : PrimeSpectrum R) :
    (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p.asIdeal) ≤ ringKrullDim R := by
  have : Nonempty (PrimeSpectrum R) := ⟨p⟩
  rw [p.height_eq_orderHeight, ringKrullDim_quotient_eq_coheight, ← WithBot.coe_add]
  change ((Order.height p + Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤
    Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun q : PrimeSpectrum R =>
    Order.height q + Order.coheight q) p)

/-- 有限次元の環では、自然数化した高さから元の高さが復元できる。 -/
lemma natCast_primeHeight_toNat [FiniteRingKrullDim R] (p : PrimeSpectrum R) :
    (p.asIdeal.height.toNat : ℕ∞) = p.asIdeal.height :=
  ENat.natCast_toNat (Ideal.height_ne_top p.isPrime.ne_top)

/-- 有限次元の環の素イデアルによる商も有限次元。 -/
lemma finiteRingKrullDim_primeQuotient [FiniteRingKrullDim R] (p : PrimeSpectrum R) :
    FiniteRingKrullDim (R ⧸ p.asIdeal) := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  refine ⟨?_, ?_⟩
  · rw [ringKrullDim_quotient_eq_coheight]
    exact WithBot.coe_ne_bot
  · exact (lt_of_le_of_lt (ringKrullDim_quotient_le p.asIdeal) ringKrullDim_lt_top).ne

/-- 高さと商の次元の和の上界の自然数版。 -/
lemma height_toNat_add_dimToNat_quotient_le [FiniteRingKrullDim R] (p : PrimeSpectrum R) :
    p.asIdeal.height.toNat + dimToNat (ringKrullDim (R ⧸ p.asIdeal)) ≤
      dimToNat (ringKrullDim R) := by
  have := finiteRingKrullDim_primeQuotient p
  have h := height_add_ringKrullDim_quotient_le p
  rw [← natCast_dimToNat_ringKrullDim (R ⧸ p.asIdeal),
    ← natCast_dimToNat_ringKrullDim R, ← natCast_primeHeight_toNat p] at h
  exact_mod_cast h

/-- `QuotSMulTop y (R/I)` の台は `R/(I + (y))` の台。 -/
lemma supportDim_quotSMulTop_quotient {R : Type u} [CommRing R] (I : Ideal R) (y : R) :
    Module.supportDim R (QuotSMulTop y (R ⧸ I)) =
      ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim]
  have : Module.support R (QuotSMulTop y (R ⧸ I)) =
      Module.support R (R ⧸ (I ⊔ Ideal.span {y})) := by
    rw [Module.support_quotSMulTop, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient, Ideal.annihilator_quotient, ← zeroLocus_span {y},
      zeroLocus_sup]
  rw [Module.supportDim, Module.supportDim, this]

end Height

end SerrePositivity
