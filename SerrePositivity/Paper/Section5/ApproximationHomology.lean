module

public import SerrePositivity.Asymptotic.MinimalTruncationComparison

/-! # 有限近似の Tor 極限と、次数に応じた代表の選択

剰余体係数の Tor の正規化極限が有限で、高次では零になることから、
支持つきランク商の対象を変えずに切り詰めを深くする。
選んだ次数で係数変更後のホモロジーを Tor と同定できるが、この同定だけでは
商上の Euler 評価と生の Tor の極限の一致を主張しない。
共通の消去冪と Koszul の有限性を使ってこの接続を完成するのが `ApproximationBetti`。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotics Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {B S : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing S]
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

/-- 有限近似の極限から、任意の固定次数で Tor を計算する支持つきの代表を選べる。
係数変更の平坦性も、`B` の正則性も必要ない。 -/
theorem exists_supported_representative_computing_tor (φ : B →+* S)
    (l : ℕ) (hs : ∀ n, 0 < s n)
    (τ : ℕ → ℝ≥0∞) (hfin : ∀ i, τ i ≠ ⊤) (hzero : ∀ i, l < i → τ i = 0)
    (hlim : ∀ i, Tendsto (fun n ↦
      (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 (τ i)))
    (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
    (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    {e : ℕ} (z : Fin e → B)
    (h : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
    (i : ℕ) :
    ∃ L : CochainComplex (FreeSequence B s) ℤ, ∃ hL : strictlyBoundedComplex _ L,
      ∃ h' : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj L hL)),
      Nonempty ((⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩ :
        (paperSupportedRank (s := s) z).FullSubcategory) ≅
        ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj L hL), h'⟩) ∧
      ∀ n, Nonempty (ModuleCat.of S (TorAlg φ i (M n)) ≅
        (baseChange φ ((evaluateComplex n).obj L)).homology (-(i : ℤ))) := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hfin hzero hlim
  obtain ⟨L, hL, ⟨eL⟩, htor⟩ := exists_minimal_representative_computing_tor M φ l K hK eK hO ho i
  have h' := (scalarSupported z).prop_of_iso eL h
  exact ⟨L, hL, h', ⟨ObjectProperty.isoMk _ eL⟩, htor⟩

/-- 有限近似の通常 Tor の極限を、同じ支持つき対象の深い代表のホモロジーへ移す。
商上の Betti 評価との一致は、この段階ではまだ主張しない。 -/
theorem exists_supported_representative_with_tor_limit (N : ModuleCat.{u} B)
    (l : ℕ) (hs : ∀ n, 0 < s n)
    (τ : ℕ → ℝ≥0∞) (hfin : ∀ i, τ i ≠ ⊤) (hzero : ∀ i, l < i → τ i = 0)
    (hlim : ∀ i, Tendsto (fun n ↦
      (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 (τ i)))
    (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
    (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    {e : ℕ} (z : Fin e → B)
    (h : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
    (i : ℕ) (ρ : ℝ≥0∞)
    (hρ : Tendsto (fun n ↦ (Module.length B (TorModule B i (M n) N) : ℝ≥0∞) / (s n : ℝ≥0∞))
      atTop (𝓝 ρ)) :
    ∃ L : CochainComplex (FreeSequence B s) ℤ, ∃ hL : strictlyBoundedComplex _ L,
      ∃ h' : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj L hL)),
      Nonempty ((⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩ :
        (paperSupportedRank (s := s) z).FullSubcategory) ≅
        ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj L hL), h'⟩) ∧
      (∀ n, Nonempty (ModuleCat.of B (TorModule B i (M n) N) ≅
        (((CategoryTheory.MonoidalCategory.tensorLeft N).mapHomologicalComplex (.up ℤ)).obj
          ((evaluateComplex n).obj L)).homology (-(i : ℤ)))) ∧
      Tendsto (fun n ↦ (Module.length B
        ((((CategoryTheory.MonoidalCategory.tensorLeft N).mapHomologicalComplex (.up ℤ)).obj
          ((evaluateComplex n).obj L)).homology (-(i : ℤ))) : ℝ≥0∞) / (s n : ℝ≥0∞))
        atTop (𝓝 ρ) := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hfin hzero hlim
  obtain ⟨L, hL, ⟨eL⟩, htor⟩ :=
    exists_minimal_representative_computing_torModule M N l K hK eK hO ho i
  have h' := (scalarSupported z).prop_of_iso eL h
  refine ⟨L, hL, h', ⟨ObjectProperty.isoMk _ eL⟩, htor, ?_⟩
  have hlen (n : ℕ) := (htor n).some.toLinearEquiv.length_eq
  simp_rw [← hlen]
  exact hρ

end SerrePositivity.Section5
