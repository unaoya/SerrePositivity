module

public import SerrePositivity.Asymptotic.NormalizedLimit
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # 正規化極限の下界と正値性 -/

@[expose] public section

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
