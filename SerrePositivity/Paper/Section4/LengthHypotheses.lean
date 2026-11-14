module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import SerrePositivity.CommutativeAlgebra.Support.Closed
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.Paper.Section3.NormComparison
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.LengthAlgebra.Normalized

/-! # 長さ代数の公式から比較の仮定へ

## 概要

有限局所代数の閉点の台と、正の冪での Koszul 消滅・商の階数公式から、Koszul 有限性、通常と正規化の Koszul Euler 数の一致、下界の商 `C/m_T C` の正値性（Corollary 2.6 の 3、`residue_length_pos_of_lengthAlgebra_values`）を導く。スペクトルの全射と有限局所整域上の階数の正値性から、係数環 `C` の非自明性も確かめる。

## 規約

正則パラメータの正則性や不変類の降下はここでは使わない。

## 使われ方

Paper/Section5（`LengthAlgebraPositivity` ほか）。
-/

@[expose] public noncomputable section

universe u

section LengthHypothesesPart

namespace SerrePositivity.Section4

open CategoryTheory Limits
open scoped ENNReal

/-- 商の長さが階数に等しいなら、§4 の C は非自明。
有限局所整域 T の階数の正値性と、零加群の長さが零であることから従う。 -/
lemma nontrivial_of_section4_quotient
    {A T C : Type u} [CommRing A] [IsDomain A] [CommRing T] [IsDomain T]
    [Algebra A T] [Module.Finite A T] [CommRing C]
    {J : Ideal C} (lam : NormalizedLength C J) (I : Ideal C)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (hq : lam.len (C ⧸ I) = (Module.finrank A T : ℝ≥0∞)) : Nontrivial C := by
  let : Module.IsTorsionFree A T :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (algebraMap_injective_of_spectrum_surjective A T hsurj)
  have hr : 0 < Module.finrank A T := Module.finrank_pos
  rcases subsingleton_or_nontrivial C with hC | hC
  · have h0 : (Module.finrank A T : ℝ≥0∞) = 0 :=
      hq.symm.trans (lam.len_eq_zero_of_subsingleton _)
    have : Module.finrank A T = 0 := by exact_mod_cast h0
    omega
  · exact hC

end SerrePositivity.Section4

end LengthHypothesesPart

section LengthAlgebraRealizationPart

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

/-- 有限な Noether 基底から来る長さの定義域のイデアルは有限生成。 -/
lemma finite_lengthAlgebra_ideal_fg
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {T C : Type u} [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Finite A T]
    [CommRing C] (ψ : T →+* C) : ((maximalIdeal T).map ψ).FG := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  exact (maximalIdeal T).fg_of_isNoetherianRing.map ψ

/-- 有限局所代数の極大イデアルから定める長さの定義域は、基底のパラメータで支持される。 -/
lemma finite_lengthAlgebra_support
    {A T C : Type u} [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [Module.Finite A T] [CommRing C] (ψ : T →+* C)
    {e : ℕ} (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A) :
    (maximalIdeal T).map ψ ≤
      (Ideal.span (Set.range (ψ ∘ algebraMap A T ∘ a))).radical := by
  have h := (Ideal.map_mono (f := ψ) (maximalIdeal_le_radical_span_of_finite T a ha)).trans
    (Ideal.map_radical_le ψ)
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
  {e : ℕ} (w : Fin e → C) (r : ℕ)
  (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
    lam.len (koszulHomologySelf (fun j ↦ w j ^ v) i) = 0)
  (hquot : ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ w j ^ v)) = ((v ^ e * r : ℕ) : ℝ≥0∞))

include hzero hquot in
/-- 正の冪での消滅と有限な商の値から、抽象層の Koszul 有限性を得る。 -/
lemma koszulFinite_of_lengthAlgebra_values : LengthAlgebra.KoszulFinite lam w := by
  intro v hv q
  exact LengthAlgebra.koszul_finite_of_zero_positive lam _ (hzero v hv)
    (by rw [hquot v hv]; exact ENNReal.natCast_ne_top _) q

include hquot in
/-- 基底パラメータの一乗での商の値は、指定された階数に等しい。 -/
lemma quotient_length_of_lengthAlgebra_values :
    lam.len (C ⧸ Ideal.span (Set.range w)) = (r : ℝ≥0∞) := by
  have h := hquot 1 one_pos
  have hw : (fun j ↦ w j ^ 1) = w := funext fun j ↦ pow_one (w j)
  rw [hw, one_pow, one_mul] at h
  exact h

include hzero hquot in
/-- 長さ代数の Koszul Euler 数は、商の公式の階数に等しい。 -/
lemma koszulEuler_of_lengthAlgebra_values : LengthAlgebra.koszulEuler lam w = (r : ℝ) := by
  have hw : (fun j ↦ w j ^ 1) = w := funext fun j ↦ pow_one (w j)
  have hz := hzero 1 one_pos
  rw [hw] at hz
  rw [LengthAlgebra.koszulEuler_eq_length_quotient lam w hz,
    quotient_length_of_lengthAlgebra_values lam w r hquot, ENNReal.toReal_natCast]

section finite

variable {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Finite A T]
  [Algebra T C] (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
  (nu : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
  (hvalues : ∀ v : ℕ, 0 < v → nu.len
    (C ⧸ Ideal.span (Set.range fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v)) =
      ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))

include ha hvalues in
/-- 商の階数公式と正の階数から、共通下界の商 `C / m_T C` の正値性を導く（論文 Corollary 2.6 の 3）。
`T/(a)T` の組成列を `C` でテンソルして、各因子が `C/m_T C` の商であることを使う。 -/
lemma residue_length_pos_of_lengthAlgebra_values (hrank : 0 < Module.finrank A T) :
    0 < nu.len (C ⧸ (maximalIdeal T).map (algebraMap T C)) := by
  let H := Ideal.span (Set.range (algebraMap A T ∘ a))
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have : IsArtinianRing (T ⧸ H) := isArtinianRing_quotient_span_of_finite A T a
    (by rw [ha]; exact (maximalIdeal.isMaximal A).isPrime.radical)
  have hH : IsFiniteLength T (T ⧸ H) :=
    isFiniteLength_of_le_radical_annihilator H _ (by
      rw [Ideal.annihilator_quotient]
      exact Ideal.le_radical)
  apply len_quotient_maximalIdeal_pos nu H hH
  have hq := quotient_length_of_lengthAlgebra_values nu
    (algebraMap T C ∘ algebraMap A T ∘ a) (Module.finrank A T) hvalues
  have hmap : H.map (algebraMap T C) =
      Ideal.span (Set.range (algebraMap T C ∘ algebraMap A T ∘ a)) := by
    dsimp only [H]
    rw [Ideal.map_span, ← Set.range_comp]
  rw [hmap, hq]
  exact_mod_cast hrank

include hvalues in
omit [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A T] in
/-- 通常の Koszul 階数公式と長さ代数の値の公式から、抽象比較の係数の一致を確認する。 -/
lemma koszulEuler_eq_of_lengthAlgebra_values
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T a = Module.finrank A T)
    (hz : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i → nu.len
      (koszulHomologySelf (fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v) i) = 0) :
    LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ a) =
      LengthAlgebra.koszulEuler nu (algebraMap T C ∘ algebraMap A T ∘ a) := by
  apply Eq.trans ?_ (koszulEuler_of_lengthAlgebra_values nu
    (algebraMap T C ∘ algebraMap A T ∘ a) (Module.finrank A T) hz hvalues).symm
  rw [ordinary_koszulEuler_eq_koszulEulerChar a hres, hχ]

end finite

end SerrePositivity.Section4

end LengthAlgebraRealizationPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Prop 4.5" (partial := component) "仮定：台付きランク商、A の正則パラメータと (4.1) の長さ条件（原典の正規化長側。Lean は有限性の引数を明示）。結論：商内の冪等元による直和因子も含む K₀ 類について、係数拡大後の正規化 Euler 評価は A の通常評価の階数倍（原典の正規化長側）。"] _root_.SerrePositivity.Section4.koszulEuler_of_lengthAlgebra_values
