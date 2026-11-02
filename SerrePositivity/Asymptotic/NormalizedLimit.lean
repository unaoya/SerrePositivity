module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import SerrePositivity.LengthAlgebra.Cone

/-! # 正規化された列の超極限

## 概要

正の整数列 s と atTop より細かい超フィルターに対し、O(s) の実数列を s で割った超極限 `normalizedLimit` を定め、有限性・加法性・非負性・有限和との交換、o(s) の列の消滅、下界と正値性を示す。一様有界な複体の列の Euler 和と超極限の交換、加群の列の長さの O(s)・o(s) 条件と正規化超極限が零である条件（短完全列での加法性）、Koszul ホモロジーの二項公式の正規化極限を与える。

## 方針

通常の漸近条件（atTop での O・o）と超極限による零条件を区別して扱う。長さは有限性を確かめてから実数にする。

## 規約

Mathlib の解析（超フィルター・漸近記法）だけを使う軽いファイル。

## 使われ方

Asymptotic の全体、Paper の §4・§5。
-/

@[expose] public noncomputable section

universe u

section NormalizedLimitPart

namespace SerrePositivity.Asymptotic

open Filter Asymptotics Topology
open scoped BigOperators

/-- 正規化列で割った実数列の超極限。収束性は別の定理で保証する。 -/
noncomputable def normalizedLimit (U : Ultrafilter ℕ) (s : ℕ → ℕ) (f : ℕ → ℝ) : ℝ :=
  limUnder (U : Filter ℕ) (fun n ↦ f n / (s n : ℝ))

/-- `O(s)` の列を正の `s` で割った列は、超フィルターに沿って収束する。 -/
lemma normalizedLimit_tendsto (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) (f : ℕ → ℝ)
    (hf : f =O[atTop] (fun n ↦ (s n : ℝ))) :
    Tendsto (fun n ↦ f n / (s n : ℝ)) (U : Filter ℕ) (𝓝 (normalizedLimit U s f)) := by
  obtain ⟨c, hc⟩ := hf.bound
  have hb : ∀ᶠ n in (U : Filter ℕ), f n / (s n : ℝ) ∈ Set.Icc (-c) c := by
    filter_upwards [hU hc] with n hn
    have hn' : ‖f n / (s n : ℝ)‖ ≤ c := by
      rw [norm_div, Real.norm_natCast, div_le_iff₀ (by exact_mod_cast hs n)]
      simpa only [Real.norm_natCast] using hn
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hn')
  obtain ⟨x, _, hx⟩ := (isCompact_Icc : IsCompact (Set.Icc (-c) c)).ultrafilter_le_nhds
    (U.map (fun n ↦ f n / (s n : ℝ))) (le_principal_iff.mpr hb)
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- 零列の正規化超極限。 -/
@[simp] lemma normalizedLimit_zero (U : Ultrafilter ℕ) (s : ℕ → ℕ) :
    normalizedLimit U s (fun _ ↦ 0) = 0 := by
  simpa [normalizedLimit] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (0 : ℝ)) (U : Filter ℕ) (𝓝 0)).limUnder_eq

/-- 通常の `o(s)` 条件は、正規化超極限の消滅を与える。 -/
lemma normalizedLimit_eq_zero_of_isLittleO (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → ℕ) (f : ℕ → ℝ)
    (hf : f =o[atTop] (fun n ↦ (s n : ℝ))) : normalizedLimit U s f = 0 :=
  (hf.tendsto_div_nhds_zero.mono_left hU).limUnder_eq

/-- 収束する二つの正規化列について超極限は加法的である。 -/
lemma normalizedLimit_add (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) (f g : ℕ → ℝ)
    (hf : f =O[atTop] (fun n ↦ (s n : ℝ)))
    (hg : g =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ f n + g n) =
      normalizedLimit U s f + normalizedLimit U s g := by
  have h := (normalizedLimit_tendsto U hU s hs f hf).add
    (normalizedLimit_tendsto U hU s hs g hg)
  simpa only [normalizedLimit, ← add_div] using h.limUnder_eq

/-- 正規化超極限は実数の定数倍と可換である。 -/
lemma normalizedLimit_const_mul (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) (f : ℕ → ℝ)
    (hf : f =O[atTop] (fun n ↦ (s n : ℝ))) (c : ℝ) :
    normalizedLimit U s (fun n ↦ c * f n) = c * normalizedLimit U s f := by
  have h := (normalizedLimit_tendsto U hU s hs f hf).const_mul c
  simpa only [normalizedLimit, ← mul_div_assoc] using h.limUnder_eq

/-- 正規化超極限は有限和と可換である。 -/
lemma normalizedLimit_sum (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) {ι : Type*} (I : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ I, f i =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ ∑ i ∈ I, f i n) =
      ∑ i ∈ I, normalizedLimit U s (f i) := by
  have h := tendsto_finsetSum I (fun i hi ↦ normalizedLimit_tendsto U hU s hs (f i) (hf i hi))
  simpa only [normalizedLimit, div_eq_mul_inv, Finset.sum_mul] using h.limUnder_eq

/-- 非負な列の正規化超極限は非負である。 -/
lemma normalizedLimit_nonneg (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) (f : ℕ → ℝ)
    (hf : f =O[atTop] (fun n ↦ (s n : ℝ))) (hf₀ : ∀ᶠ n in (U : Filter ℕ), 0 ≤ f n) :
    0 ≤ normalizedLimit U s f :=
  ge_of_tendsto (normalizedLimit_tendsto U hU s hs f hf)
    (hf₀.mono fun _ hn ↦ div_nonneg hn (Nat.cast_nonneg _))

end SerrePositivity.Asymptotic

end NormalizedLimitPart

section NormalizedLowerBoundPart

namespace SerrePositivity.Asymptotic

open Filter Asymptotics Topology
open scoped ENNReal

/-- `O(s)` の列の不等式は正規化超極限でも保たれる。 -/
lemma normalizedLimit_mono (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) (f g : ℕ → ℝ)
    (hf : f =O[atTop] (fun n ↦ (s n : ℝ)))
    (hg : g =O[atTop] (fun n ↦ (s n : ℝ)))
    (hfg : ∀ᶠ n in (U : Filter ℕ), f n ≤ g n) :
    normalizedLimit U s f ≤ normalizedLimit U s g :=
  le_of_tendsto_of_tendsto (normalizedLimit_tendsto U hU s hs f hf)
    (normalizedLimit_tendsto U hU s hs g hg)
    (hfg.mono fun _ hn ↦ div_le_div_of_nonneg_right hn (Nat.cast_nonneg _))

/-- 有限値への通常の ENNReal 収束を、実数値の正規化超極限へ移す。 -/
lemma normalizedLimit_eq_of_ennreal_tendsto (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → ℕ) (f : ℕ → ℝ≥0∞)
    {L : ℝ≥0∞} (hL : L ≠ ⊤)
    (hf : Tendsto (fun n ↦ f n / (s n : ℝ≥0∞)) atTop (𝓝 L)) :
    normalizedLimit U s (fun n ↦ (f n).toReal) = L.toReal := by
  have h := (ENNReal.continuousAt_toReal hL).tendsto.comp (hf.mono_left hU)
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_natCast,
    normalizedLimit] using h.limUnder_eq

/-- 近似加群の長さの極限と生成元数による項ごとの上界から、生成元数の極限の下界を得る。 -/
lemma normalizedLimit_generator_lower_bound (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (f b : ℕ → ℝ) (hb : b =O[atTop] (fun n ↦ (s n : ℝ)))
    {L c : ℝ} (hf : Tendsto (fun n ↦ f n / (s n : ℝ)) atTop (𝓝 L))
    (hbound : ∀ n, f n ≤ c * b n) : L ≤ c * normalizedLimit U s b := by
  have h := (normalizedLimit_tendsto U hU s hs b hb).const_mul c
  apply le_of_tendsto_of_tendsto (hf.mono_left hU) h
  exact Eventually.of_forall fun n ↦ by
    simpa only [← mul_div_assoc] using
      div_le_div_of_nonneg_right (hbound n) (Nat.cast_nonneg (s n) : (0 : ℝ) ≤ s n)

/-- 正の長さを近似する加群では、生成元数の正規化超極限も正になる。 -/
lemma normalizedLimit_generator_pos (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (f b : ℕ → ℝ) (hb : b =O[atTop] (fun n ↦ (s n : ℝ)))
    {L c : ℝ} (hf : Tendsto (fun n ↦ f n / (s n : ℝ)) atTop (𝓝 L))
    (hbound : ∀ n, f n ≤ c * b n) (hL : 0 < L) (hc : 0 ≤ c) :
    0 < normalizedLimit U s b := by
  have h := normalizedLimit_generator_lower_bound U hU s hs f b hb hf hbound
  nlinarith

end SerrePositivity.Asymptotic

end NormalizedLowerBoundPart

section EulerLimitPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics
open scoped BigOperators

/-- 共通の有限支持をもつ実数列の族では、有限支持和と超極限を交換できる。 -/
lemma normalizedLimit_finsum (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n) {ι : Type*} (I : Finset ι) (f : ι → ℕ → ℝ)
    (hsupp : ∀ n i, i ∉ I → f i n = 0)
    (hf : ∀ i ∈ I, f i =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ ∑ᶠ i, f i n) =
      ∑ᶠ i, normalizedLimit U s (f i) := by
  have hsum (n : ℕ) : (∑ᶠ i, f i n) = ∑ i ∈ I, f i n := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    exact hi (hsupp n i hn)
  have hlim : (∑ᶠ i, normalizedLimit U s (f i)) =
      ∑ i ∈ I, normalizedLimit U s (f i) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    apply hi
    change normalizedLimit U s (f i) = 0
    have heq : f i = fun _ ↦ 0 := funext fun n ↦ hsupp n i hn
    rw [heq, normalizedLimit_zero]
  simp_rw [hsum, hlim]
  exact normalizedLimit_sum U hU s hs I f hf

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 共通の有限な項の支持から、同じ範囲でのホモロジーの長さの消滅が従う。 -/
lemma lengthHomology_zero_outside (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Finset ℤ) (hP : ∀ n i, i ∉ I → IsZero ((P n).X i))
    (n : ℕ) (i : ℤ) (hi : i ∉ I) : lam.len ((P n).homology i) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X (P n) i (hP n i hi))
  exact lam.len_eq_zero_of_subsingleton _

/-- 共通有限支持と各次数の長さの `O(s)` 評価から、Euler 値の列も `O(s)` となる。 -/
lemma lambdaEuler_isBigO (s : ℕ → ℕ)
    (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (I : Finset ℤ)
    (hP : ∀ n i, i ∉ I → IsZero ((P n).X i))
    (hbound : ∀ i, (fun n ↦ (lam.len ((P n).homology i)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ))) :
    (fun n ↦ lambdaEuler lam (P n)) =O[atTop] (fun n ↦ (s n : ℝ)) := by
  have heq (n : ℕ) : lambdaEuler lam (P n) =
      ∑ i ∈ I, ((i.negOnePow : ℤ) : ℝ) * (lam.len ((P n).homology i)).toReal := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hn
    apply hi
    simp only [lengthHomology_zero_outside lam P I hP n i hn, ENNReal.toReal_zero, mul_zero]
  simp_rw [heq]
  exact IsBigO.fun_sum (fun i _ ↦ (hbound i).const_mul_left _)

/-- 共通有界な複体列では、各段の Euler 評価の超極限は、次数別超極限の Euler 和に等しい。 -/
lemma normalizedLimit_lambdaEuler (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (I : Finset ℤ)
    (hP : ∀ n i, i ∉ I → IsZero ((P n).X i))
    (hbound : ∀ i, (fun n ↦ (lam.len ((P n).homology i)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ lambdaEuler lam (P n)) =
      ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) *
        normalizedLimit U s (fun n ↦ (lam.len ((P n).homology i)).toReal) := by
  unfold lambdaEuler
  rw [normalizedLimit_finsum U hU s hs I _ (fun n i hi ↦ by
    rw [lengthHomology_zero_outside lam P I hP n i hi, ENNReal.toReal_zero, mul_zero])
    (fun i _ ↦ (hbound i).const_mul_left _)]
  congr 1
  funext i
  exact normalizedLimit_const_mul U hU s hs _ (hbound i) _

end SerrePositivity.Asymptotic

end EulerLimitPart

section LengthFamiliesPart

namespace SerrePositivity.Asymptotic

open Filter Asymptotics

/-- 非負の列の項ごとの不等式は `O` 評価を与える。 -/
lemma isBigO_of_nonneg_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n) :
    f =O[atTop] g :=
  IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by
    rw [one_mul, Real.norm_of_nonneg (hf n), Real.norm_of_nonneg ((hf n).trans (hfg n))]
    exact hfg n)

/-- 非負の列の和が `O(s)` であることと、各列が `O(s)` であることは同値。 -/
lemma nonneg_add_isBigO_iff {f g s : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (fun n ↦ f n + g n) =O[atTop] s ↔ f =O[atTop] s ∧ g =O[atTop] s := by
  constructor
  · intro h
    exact ⟨(isBigO_of_nonneg_le hf (fun n ↦ le_add_of_nonneg_right (hg n))).trans h,
      (isBigO_of_nonneg_le hg (fun n ↦ le_add_of_nonneg_left (hf n))).trans h⟩
  · rintro ⟨h₁, h₂⟩
    exact h₁.add h₂

/-- 非負の列の和が通常の `o(s)` であることと、各列が `o(s)` であることは同値。 -/
lemma nonneg_add_isLittleO_iff {f g s : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (fun n ↦ f n + g n) =o[atTop] s ↔ f =o[atTop] s ∧ g =o[atTop] s := by
  constructor
  · intro h
    exact ⟨(isBigO_of_nonneg_le hf (fun n ↦ le_add_of_nonneg_right (hg n))).trans_isLittleO h,
      (isBigO_of_nonneg_le hg (fun n ↦ le_add_of_nonneg_left (hf n))).trans_isLittleO h⟩
  · rintro ⟨h₁, h₂⟩
    exact h₁.add h₂

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (M N P : ℕ → ModuleCat.{u} R) (f : ∀ n, M n →ₗ[R] N n) (g : ∀ n, N n →ₗ[R] P n)
  (hf : ∀ n, Function.Injective (f n)) (hg : ∀ n, Function.Surjective (g n))
  (hex : ∀ n, Function.Exact (f n) (g n)) (htors : ∀ n, IsPowTorsion J (N n))
  (hfin : ∀ n, lam.len (N n) ≠ ⊤)

include hf hg hex htors hfin in
/-- 有限長の短完全列の族について、長さの実数化は項ごとに加法的である。 -/
lemma lengthFamily_toReal_add (n : ℕ) :
    (lam.len (N n)).toReal = (lam.len (M n)).toReal + (lam.len (P n)).toReal := by
  have h := lam.len_add_of_exact _ _ _ (f n) (g n) (hf n) (hg n) (hex n) (htors n)
  have hM := ne_top_of_le_ne_top (hfin n) (lam.len_le_of_injective (f n) (hf n) (htors n))
  have hP := ne_top_of_le_ne_top (hfin n) (lam.len_le_of_surjective (g n) (hg n) (htors n))
  rw [h, ENNReal.toReal_add hM hP]

include hf hg hex htors hfin in
/-- 短完全列の族の中央の長さが `O(s)` であることは、両端の同じ条件と同値。 -/
lemma lengthFamily_isBigO_iff (s : ℕ → ℝ) :
    (fun n ↦ (lam.len (N n)).toReal) =O[atTop] s ↔
      (fun n ↦ (lam.len (M n)).toReal) =O[atTop] s ∧
      (fun n ↦ (lam.len (P n)).toReal) =O[atTop] s := by
  simp_rw [lengthFamily_toReal_add lam M N P f g hf hg hex htors hfin]
  exact nonneg_add_isBigO_iff (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)

include hf hg hex htors hfin in
/-- 短完全列の族における通常の `o(s)` 条件は Serre 条件を満たす。 -/
lemma lengthFamily_isLittleO_iff (s : ℕ → ℝ) :
    (fun n ↦ (lam.len (N n)).toReal) =o[atTop] s ↔
      (fun n ↦ (lam.len (M n)).toReal) =o[atTop] s ∧
      (fun n ↦ (lam.len (P n)).toReal) =o[atTop] s := by
  simp_rw [lengthFamily_toReal_add lam M N P f g hf hg hex htors hfin]
  exact nonneg_add_isLittleO_iff (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)

include hf hg hex htors hfin in
/-- 短完全列の族の長さに正規化超極限を施しても加法性が保たれる。 -/
lemma lengthFamily_normalizedLimit_add (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hN : (fun n ↦ (lam.len (N n)).toReal) =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ (lam.len (N n)).toReal) =
      normalizedLimit U s (fun n ↦ (lam.len (M n)).toReal) +
      normalizedLimit U s (fun n ↦ (lam.len (P n)).toReal) := by
  obtain ⟨hM, hP⟩ := (lengthFamily_isBigO_iff lam M N P f g hf hg hex htors hfin _).1 hN
  simp_rw [lengthFamily_toReal_add lam M N P f g hf hg hex htors hfin]
  exact normalizedLimit_add U hU s hs _ _ hM hP

include hf hg hex htors hfin in
/-- 正規化超極限が零となる条件は、短完全列の族に対して Serre 条件を満たす。 -/
lemma lengthFamily_normalizedLimit_zero_iff (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hN : (fun n ↦ (lam.len (N n)).toReal) =O[atTop] (fun n ↦ (s n : ℝ))) :
    normalizedLimit U s (fun n ↦ (lam.len (N n)).toReal) = 0 ↔
      normalizedLimit U s (fun n ↦ (lam.len (M n)).toReal) = 0 ∧
      normalizedLimit U s (fun n ↦ (lam.len (P n)).toReal) = 0 := by
  rw [lengthFamily_normalizedLimit_add lam M N P f g hf hg hex htors hfin U hU s hs hN]
  obtain ⟨hM, hP⟩ := (lengthFamily_isBigO_iff lam M N P f g hf hg hex htors hfin _).1 hN
  have h₁ := normalizedLimit_nonneg U hU s hs _ hM
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  have h₃ := normalizedLimit_nonneg U hU s hs _ hP
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  exact add_eq_zero_iff_of_nonneg h₁ h₃

end SerrePositivity.Asymptotic

end LengthFamiliesPart

section KoszulHomologyLimitPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter Asymptotics

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 各段の零ホモトピーと長さの有界性から、極限も同じ二項公式を満たす。 -/
theorem normalizedLimit_koszul_null_binomial {e : ℕ} (x : Fin e → R)
    (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ n j, Nonempty (Homotopy (smulId (x j) (P n)) 0))
    (ht : ∀ n q, IsPowTorsion J ((P n).homology q))
    (hfin : ∀ n q, lam.len ((P n).homology q) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hO : ∀ q, (fun n ↦ (lam.len ((P n).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ))) (q : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len ((koszulComplexOn x (P n)).homology q)).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        normalizedLimit U s (fun n ↦ (lam.len ((P n).homology (q + j))).toReal) := by
  simp_rw [lambdaHomology_koszul_null_binomial lam x _ (hx _) (ht _) (hfin _)]
  rw [normalizedLimit_sum U hU s hs _ _
    (fun (j : ℕ) _ ↦ (hO (q + j)).const_mul_left (e.choose j : ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  exact normalizedLimit_const_mul U hU s hs _ (hO (q + j)) _

end SerrePositivity.Asymptotic

end KoszulHomologyLimitPart
