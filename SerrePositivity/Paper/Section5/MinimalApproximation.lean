module

public import SerrePositivity.Asymptotic.MinimalResolutionFamily
public import SerrePositivity.Paper.Section5.ApproximationLowerBound

/-! # 有限近似から極小な自由複体列と正の零次階数を構成する

有限近似の Betti 数の `O(s)` 評価から、極小分解を切り詰めた自由複体列を作る。
加群を一様に消すイデアルと正の長さの極限から、零次階数の正規化超極限は正になる。
階数と Tor の長さの一致・極小性を追加の入力として要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotics Asymptotic
open scoped ENNReal

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- Lemma 5.4 型の有限近似から、振幅・極小性・正の零次階数をもつ実際の自由複体列を得る。
商での支持、および係数変更後の Euler 評価との接続は別の主張である。 -/
theorem exists_minimal_approximation_sequence
    (M : ℕ → ModuleCat.{u} B) (hM : ∀ n, Module.Finite B (M n))
    (l : ℕ) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hbetti : ∀ i ≤ l,
      (fun n ↦ ((Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (I : Ideal B) (hI : ∀ n, ∀ y ∈ I, ∀ m : M n, y • m = 0)
    (hIfin : Module.length B (B ⧸ I) ≠ ⊤)
    {L : ℝ≥0∞} (hLfin : L ≠ ⊤) (hLpos : 0 < L)
    (hlim : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ F : CochainComplex (FreeSequence B s) ℤ,
      (F.IsStrictlyGE (-(l : ℤ)) ∧ F.IsStrictlyLE 0) ∧
      (∀ n, Nonempty ((evaluateComplex n).obj F ≅
        MinimalFreeResolution.truncated (letI := hM n; FGModuleCat.of B (M n)) l)) ∧
      (∀ i ≤ l, ∀ n, ((F.X (-(i : ℤ))).rank n : ℕ∞) =
        Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))) ∧
      (∀ n (x : Fin ((F.X (-1)).rank n) → B) (j : Fin ((F.X 0).rank n)),
        F.d (-1) 0 n x j ∈ maximalIdeal B) ∧
      0 < normalizedLimit U s (fun n ↦ ((F.X 0).rank n : ℝ)) := by
  let (n : ℕ) := hM n
  let N (n : ℕ) := FGModuleCat.of B (M n)
  obtain ⟨F, hb, he, hr, hm⟩ := exists_minimal_truncated_sequence N l hbetti
  refine ⟨F, hb, he, hr, hm, ?_⟩
  apply finiteApproximation_rank_pos M hM I hI hIfin s (F.X 0).rank hs
    (F.X 0).rank_isBigO ?_ hLfin hlim U hU hLpos
  intro n
  simpa only [Nat.cast_zero, neg_zero] using (hr 0 (Nat.zero_le l) n).symm

end SerrePositivity.Section5
