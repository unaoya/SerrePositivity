module

public import SerrePositivity.Asymptotic.MinimalTruncationComparison

/-! # 有限近似の Tor 極限から Betti 数の増大条件へ

剰余体係数の Tor の正規化極限が有限で、高次では零になることから、
切り詰めに必要な `O(s)` と `o(s)` を得る。
商上のホモロジー評価との同定は `ApproximationBetti` で行う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotics Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  (M : ℕ → FGModuleCat.{u} B) {s : ℕ → ℕ}

/-- 有限近似の剰余体 Tor の極限から、必要な `O(s)` と `o(s)` を取り出す。 -/
lemma betti_growth_of_approximation_limits (l : ℕ) (hs : ∀ n, 0 < s n)
    (τ : ℕ → ℝ≥0∞) (hfin : ∀ i, τ i ≠ ⊤) (hzero : ∀ i, l < i → τ i = 0)
    (hlim : ∀ i, Tendsto (fun n ↦
      (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 (τ i))) :
    (∀ i ≤ l,
      (fun n ↦ ((Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ))) ∧
    (∀ i, l < i →
      (fun n ↦ ((Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) := by
  constructor
  · intro i _
    simpa only [MinimalFreeResolution.length_tor, ENat.toNat_natCast] using
      minimal_rank_isBigO_of_tendsto M i hs (hfin i) (hlim i)
  · intro i hi
    have h := hlim i
    rw [hzero i hi] at h
    simpa only [MinimalFreeResolution.length_tor, ENat.toNat_natCast] using
      minimal_rank_isLittleO_of_tendsto_zero M i hs h

end SerrePositivity.Section5
