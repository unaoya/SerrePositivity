module

public import SerrePositivity.Paper.Section5.ParameterQuotient
public import SerrePositivity.Asymptotic.NormalizedLowerBound

/-! # 有限近似から生成元数の正の下界へ

Lemma 5.4 の実際の長さの収束と、各加群を消すイデアルを使う。
零次の階数が `Tor₀(M,k)` の長さに一致することは極小分解側の入力として分離する。
商環 `B` の正則性は要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Asymptotics Topology IsLocalRing
open scoped ENNReal

variable {B : Type u} [CommRing B] [IsLocalRing B]
  (M : ℕ → ModuleCat.{u} B) (hM : ∀ n, Module.Finite B (M n))
  (I : Ideal B) (hI : ∀ n, ∀ y ∈ I, ∀ m : M n, y • m = 0)
  (hIfin : Module.length B (B ⧸ I) ≠ ⊤)
  (s b : ℕ → ℕ) (hs : ∀ n, 0 < s n)
  (hb : (fun n ↦ (b n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)))
  (hbeta : ∀ n, Module.length B (TorModule B 0 (M n) (B ⧸ maximalIdeal B)) = b n)
  {L : ℝ≥0∞} (hLfin : L ≠ ⊤)
  (hlim : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 L))
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)

include hM hI hIfin hs hb hbeta hLfin hlim hU in
/-- 有限近似の正規化生成元数は `λ(U) / ℓ(B/I)` 以上。
除算せずに書くことで、長さ零や空の自由加群も同じ主張で扱う。 -/
theorem finiteApproximation_rank_lower_bound :
    L.toReal ≤ (Module.length B (B ⧸ I) : ℝ≥0∞).toReal *
      Asymptotic.normalizedLimit U s (fun n ↦ (b n : ℝ)) := by
  have hreal : Tendsto
      (fun n ↦ (Module.length B (M n) : ℝ≥0∞).toReal / (s n : ℝ)) atTop (𝓝 L.toReal) := by
    simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_natCast] using
      (ENNReal.continuousAt_toReal hLfin).tendsto.comp hlim
  apply Asymptotic.normalizedLimit_generator_lower_bound U hU s hs _ _ hb hreal
  intro n
  have := hM n
  have h := length_le_tor_zero_mul (M n) I (hI n)
  rw [hbeta n] at h
  have hf : (b n : ℝ≥0∞) * (Module.length B (B ⧸ I) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by exact_mod_cast hIfin)
  have hr := ENNReal.toReal_mono hf h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm] using hr

include hM hI hIfin hs hb hbeta hLfin hlim hU in
/-- 正の有限長さを近似する加群の極小生成元数の正規化超極限は正。 -/
theorem finiteApproximation_rank_pos (hL : 0 < L) :
    0 < Asymptotic.normalizedLimit U s (fun n ↦ (b n : ℝ)) := by
  have h := finiteApproximation_rank_lower_bound M hM I hI hIfin s b hs hb hbeta hLfin hlim U hU
  have hp : 0 < L.toReal := ENNReal.toReal_pos (ne_of_gt hL) hLfin
  have hc : 0 ≤ (Module.length B (B ⧸ I) : ℝ≥0∞).toReal := ENNReal.toReal_nonneg
  nlinarith

end SerrePositivity.Section5
