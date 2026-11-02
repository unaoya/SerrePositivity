module

public import SerrePositivity.Paper.Section4.RankLowerBound
public import SerrePositivity.Paper.Section5.ParameterQuotient
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.Asymptotic.Minimal

/-! # 有限近似から極小な自由複体の列へ

## 概要

有限近似の剰余体係数の Tor の正規化極限が有限で高次で零になることから、切り詰めに要る Betti 数の `O(s)`・`o(s)` を得て、極小分解を切り詰めた自由複体の列を作る。Lemma 5.4 の長さの収束と各加群を消すイデアルから零次の階数の正規化超極限が正になること、商でのスカラーの零作用と台を加えてランク商の対象を作ることを与える。

## 規約

商環 `B` の正則性は要求しない。Paper/Section5/ParameterQuotient と Paper/Section4/RankLowerBound の切り詰めを使うので Asymptotic には置かない。

## 使われ方

`SecondComparison`・`Positivity`。
-/

@[expose] public noncomputable section

universe u

section ApproximationHomologyPart

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

end ApproximationHomologyPart

section ApproximationLowerBoundPart

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

end ApproximationLowerBoundPart

section MinimalApproximationPart

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

end MinimalApproximationPart

section SupportedApproximationPart

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

end SupportedApproximationPart
