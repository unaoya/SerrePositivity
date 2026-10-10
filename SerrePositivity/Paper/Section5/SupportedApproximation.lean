module

public import SerrePositivity.Paper.Section5.MinimalApproximation
public import SerrePositivity.Asymptotic.MinimalSupport

/-! # 有限近似から支持をもつランク商の対象を構成する

極小分解の切り詰め、極小性、正の零次階数に、商でのスカラーの零作用と支持を加える。
必要な漸近条件は、残す Betti 数の `O(s)` と直前の Betti 数の `o(s)` である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotics Asymptotic
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- 有限近似から、支持・振幅・極小性・正の零次階数を備えた複体列を構成する。
支持はランク商で証明し、切り詰め自体の一様な零ホモトピーは仮定しない。 -/
theorem exists_supported_minimal_approximation
    (M : ℕ → ModuleCat.{u} B) (hM : ∀ n, Module.Finite B (M n))
    (l : ℕ) (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hbetti : ∀ i ≤ l,
      (fun n ↦ ((Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (hsmall : (fun n ↦ ((Module.length B
      (TorModule B (l + 1) (M n) (B ⧸ maximalIdeal B))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (I : Ideal B) (hI : ∀ n, ∀ y ∈ I, ∀ m : M n, y • m = 0)
    (hIfin : Module.length B (B ⧸ I) ≠ ⊤)
    {L : ℝ≥0∞} (hLfin : L ≠ ⊤) (hLpos : 0 < L)
    (hlim : Tendsto (fun n ↦ (Module.length B (M n) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 L))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {e : ℕ} (z : Fin e → B) (N : ℕ) (hN : 0 < N) (hz : ∀ j, z j ^ N ∈ I) :
    ∃ F : CochainComplex (FreeSequence B s) ℤ,
      ∃ hb : F.IsStrictlyGE (-(l : ℤ)) ∧ F.IsStrictlyLE 0,
      (∀ n, Nonempty ((evaluateComplex n).obj F ≅
        MinimalFreeResolution.truncated (letI := hM n; FGModuleCat.of B (M n)) l)) ∧
      (∀ i ≤ l, ∀ n, ((F.X (-(i : ℤ))).rank n : ℕ∞) =
        Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B))) ∧
      (∀ n (x : Fin ((F.X (-1)).rank n) → B) (j : Fin ((F.X 0).rank n)),
        F.d (-1) 0 n x j ∈ maximalIdeal B) ∧
      0 < normalizedLimit U s (fun n ↦ ((F.X 0).rank n : ℝ)) ∧
      paperSupportedRank z ((paperSequenceFunctor B s).obj
        (sequenceHomotopyObj F ⟨-(l : ℤ), 0, hb.1, hb.2⟩)) ∧
      ∀ j, z j ^ N • 𝟙 ((paperSequenceFunctor B s).obj
        (sequenceHomotopyObj F ⟨-(l : ℤ), 0, hb.1, hb.2⟩)) = 0 := by
  obtain ⟨F, hb, he, hr, hm, hp⟩ := exists_minimal_approximation_sequence M hM l s hs
    hbetti I hI hIfin hLfin hLpos hlim U hU
  let (n : ℕ) := hM n
  let M' (n : ℕ) := FGModuleCat.of B (M n)
  have hx (j : Fin e) : z j ^ N • 𝟙 ((paperSequenceFunctor B s).obj
      (sequenceHomotopyObj F ⟨-(l : ℤ), 0, hb.1, hb.2⟩)) = 0 := by
    apply minimal_truncated_paper_scalar_zero M' l F _ he hsmall (z j ^ N)
    intro n
    ext m
    exact hI n (z j ^ N) (hz j) m
  exact ⟨F, hb, he, hr, hm, hp, ⟨N, hN, hx⟩, hx⟩

end SerrePositivity.Section5
