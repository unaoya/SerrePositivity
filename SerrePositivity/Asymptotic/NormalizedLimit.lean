module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Compactness.Compact

/-!
# 正規化された列の超極限

正の整数列 `s` と `atTop` より細かい超フィルターに対し、`O(s)` の実数列を
`s` で割って極限を取る。有限性・加法性・非負性・有限和との交換と、
`o(s)` の列の消滅を証明する。通常の漸近条件と超極限による零条件は区別する。
ここで得る数値評価だけでは、商の後で初めて台をもつ対象の評価はまだ定義されない。
-/

@[expose] public section

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
