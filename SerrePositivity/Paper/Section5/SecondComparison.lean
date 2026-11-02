module

public import SerrePositivity.Paper.Section4.SymmetricComparison
public import SerrePositivity.Paper.Section4.RankQuotient
public import SerrePositivity.Paper.Section5.Approximation
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.Paper.Section4.RankLowerBound
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.LengthAlgebra.Normalized
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.Paper.Section5.FirstComparison
public import SerrePositivity.HomologicalAlgebra.KoszulOrdinaryLength

/-! # 第二のノルム比較（論文 (5.18)）

## 概要

論文の台つき圏の実際の群作用について、通常評価の群不変性から共通の共役和比較の一方が群の位数倍になり、第二比較 `|H| · c_σ = Σ_γ b_{σ,γ}` を得る。有限近似の Tor 極限を通常評価と同定し（近似先の写像を `twistedAlgebraMap` とすると `c_σ`）、正則基底のパラメータへ台を変え、剰余体係数の極限から商の Betti・Euler 評価へ接続する。

## 方針

有限近似側と正則基底側の台は異なってよく、同じ複体の列の評価を移して接続する。通常の収束値を用いる結論は超フィルターの選択によらない。

## 規約

長さ付き代数の長さの群不変性や、群が作用する環との同変性は要求しない。Koszul Euler 数の一致と不変類の降下は個別の入力。

## 使われ方

`Section5/Positivity`。
-/

@[expose] public noncomputable section

universe u

section SecondComparisonPart

namespace SerrePositivity.Section5

open CategoryTheory Filter IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing T] [Nontrivial T] [Algebra A T] [CommRing C] [Nontrivial C]
  {G : Type u} [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (ψ : T →+* C) {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  {e : ℕ} (a : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (ψ ∘ algebraMap A T ∘ a))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (ψ ∘ algebraMap A T ∘ a))
  (hord : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (algebraMap A T ∘ a))
  (ha : Ideal.span (Set.range a) = maximalIdeal A) (hKos : IsKoszulResolution a)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ a) =
    LengthAlgebra.koszulEuler lam (ψ ∘ algebraMap A T ∘ a))
  (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
    (∀ g : G, g • y = y) → ∃ (n : ℕ)
      (x : TriangulatedK0 (paperSupportedRank (s := s) a).FullSubcategory),
      0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) a) x)

set_option maxHeartbeats 800000 in
-- 三つの係数環の支持圏と、実際の群作用をもつ K₀ の比較に必要。
include ha hKos hc hdesc in
/-- 第二比較の共通部分。通常 Euler 数の群の位数倍が、正規化評価の共役和に等しい。 -/
theorem secondComparison_of_complex
    (K : CochainComplex (FreeSequence T s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (algebraMap A T ∘ a)
      ((paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK))) :
    (Fintype.card G : ℝ) * paperRankEulerK0 (NormalizedLength.ordinary T) Submodule.fg_bot
      (algebraMap A T ∘ a) bot_le hord U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩) =
    ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
      (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩) := by
  have he := Section4.symmetricPaperEuler_conjSum_eq (algebraMap A T) (RingHom.id T) ψ
    (NormalizedLength.ordinary T) lam Submodule.fg_bot hfg a bot_le hJ hord hfin
    ha hKos U hU hs hc hdesc
    (TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj (sequenceHomotopyObj K hK), h⟩)
  rw [paperBaseChangeEulerK0_id] at he
  have hconst (g : G) := paperOrdinaryEulerK0_smul U hU hs K hK a hord h g
  simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he

variable {B : Type u} [CommRing B] [Nontrivial B] (φ : B →+* T)
  {f : ℕ} (z : Fin f → B)
  (hordB : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (φ ∘ z))

set_option maxHeartbeats 800000 in
-- 近似側と正則基底側の支持部分圏をまたぐ評価の比較に必要。
include hord ha hKos hc hdesc in
/-- 有限近似側のパラメータで計算した通常評価を、第二比較の支持圏へ移す。 -/
theorem secondComparison_of_baseChangedComplex
    (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hB : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
    (hT : paperSupportedRank (algebraMap A T ∘ a) ((paperSequenceFunctor T s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)))) :
    (Fintype.card G : ℝ) * paperBaseChangeEulerK0 φ z (NormalizedLength.ordinary T)
      Submodule.fg_bot bot_le hordB U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), hB⟩) =
    ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
      (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj
        (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
          (changeRing_strictlyBounded φ K hK)), hT⟩) := by
  rw [paperBaseChangeEulerK0_complex_support_change φ z (NormalizedLength.ordinary T)
    Submodule.fg_bot bot_le hordB U hU hs (algebraMap A T ∘ a) bot_le hord K hK hB hT]
  exact secondComparison_of_complex ψ lam hfg a hJ hfin hord ha hKos U hU hs hc hdesc _ _ hT

end SerrePositivity.Section5

end SecondComparisonPart

section ApproximationBettiPart

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {B S : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing S] (φ : B →+* S) (M : ℕ → FGModuleCat.{u} B) {s : ℕ → ℕ}
  (l : ℕ) (hs : ∀ n, 0 < s n)
  (τ : ℕ → ℝ≥0∞) (hτfin : ∀ i, τ i ≠ ⊤) (hτzero : ∀ i, l < i → τ i = 0)
  (hτlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (τ i)))
  (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
  (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
  {e : ℕ} (z : Fin e → B)
  (h : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0)
  {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)

section Nontrivial

variable [Nontrivial S]

include hτfin hτzero hτlim eK hv hM in
/-- 商の Euler 評価は有限近似の Tor 極限の有限交代和になる。 -/
theorem paperBaseChangeEulerK0_eq_of_approximation_limits (ρ : ℕ → ℝ≥0∞)
    (hρ : ∀ i, ρ i ≠ ⊤)
    (hlim : ∀ i, Tendsto (fun n ↦ lam.len (TorAlg φ i (M n)) / (s n : ℝ≥0∞))
      atTop (𝓝 (ρ i))) :
    paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
      ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (ρ i).toReal := by
  obtain ⟨hO, ho⟩ := betti_growth_of_approximation_limits M l hs τ hτfin hτzero hτlim
  rw [paperBaseChangeEulerK0_eq_minimal_tor_limits φ M z lam hfg hJ hfin U hU hs
    l K hK eK hO ho h v hv hM]
  congr 1
  funext i
  rw [normalizedLimit_eq_of_ennreal_tendsto U hU s _ (hρ i) (hlim i)]

section Ordinary

variable [Algebra B S]

local notation "lamB" =>
  NormalizedLength.comap (algebraMap B S) (NormalizedLength.ordinary B) ⊥ (by simp)

end Ordinary
end Nontrivial

section OrdinaryResidue

variable [Algebra B S] [IsLocalRing S]
  (hres : Function.Surjective ((residue S).comp (algebraMap B S)))
  (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
    (NormalizedLength.ordinary S).len
      ((koszulComplex (fun j ↦ algebraMap B S (z j) ^ v)).homology q) ≠ ⊤)

include hτfin hτzero hτlim eK hv hM hres in
/-- 共通剰余体の下で、通常 Euler 評価は有限近似の通常 Tor 極限の交代和に一致する。 -/
theorem paperOrdinaryEulerK0_eq_of_common_residueField_limits (ρ : ℕ → ℝ≥0∞)
    (hρ : ∀ i, ρ i ≠ ⊤)
    (hlim : ∀ i, Tendsto (fun n ↦ (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) /
      (s n : ℝ≥0∞)) atTop (𝓝 (ρ i))) :
    paperBaseChangeEulerK0 (algebraMap B S) z (NormalizedLength.ordinary S)
      Submodule.fg_bot bot_le hfinS U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), h⟩) =
      ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (ρ i).toReal := by
  apply paperBaseChangeEulerK0_eq_of_approximation_limits (algebraMap B S) M l hs τ
    hτfin hτzero hτlim K hK eK z h v hv hM (NormalizedLength.ordinary S)
    Submodule.fg_bot bot_le hfinS U hU ρ hρ
  intro i
  have he (n : ℕ) : (NormalizedLength.ordinary S).len (TorAlg (algebraMap B S) i (M n)) =
      (Module.length B (TorModule B i (M n) S) : ℝ≥0∞) := by
    let N := ModuleCat.of S (TorAlg (algebraMap B S) i (M n))
    exact congrArg (fun x : ℕ∞ ↦ (x : ℝ≥0∞))
      ((length_restrictScalars_eq hres N).symm.trans
        (length_restrictScalars_torAlg_comm (M n) i))
  simpa only [he] using hlim i

end OrdinaryResidue

end SerrePositivity.Section5

end ApproximationBettiPart

section ApproximationSecondComparisonPart

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing Asymptotic
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {A B T C R D : Type u}
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Algebra B T]
  [CommRing C] [Nontrivial C] [CommRing R] [CommRing D] [Module R T]
  {G : Type u} [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
  (ψ : T →+* C) {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  {e : ℕ} (a : Fin e → A)
  (hJ : J ≤ (Ideal.span (Set.range (ψ ∘ algebraMap A T ∘ a))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (ψ ∘ algebraMap A T ∘ a))
  (hord : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (algebraMap A T ∘ a))
  (ha : Ideal.span (Set.range a) = maximalIdeal A) (hKos : IsKoszulResolution a)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ a) =
    LengthAlgebra.koszulEuler lam (ψ ∘ algebraMap A T ∘ a))
  (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ a)).FullSubcategory,
    (∀ g : G, g • y = y) → ∃ (n : ℕ)
      (x : TriangulatedK0 (paperSupportedRank (s := s) a).FullSubcategory),
      0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) a) x)
  (M : ℕ → FGModuleCat.{u} B) (l : ℕ)
  (τ : ℕ → ℝ≥0∞) (hτfin : ∀ i, τ i ≠ ⊤) (hτzero : ∀ i, l < i → τ i = 0)
  (hτlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) (B ⧸ maximalIdeal B)) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (τ i)))
  (K : CochainComplex (FreeSequence B s) ℤ) (hK : strictlyBoundedComplex _ K)
  (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
  {f : ℕ} (z : Fin f → B)
  (hB : paperSupportedRank z ((paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0)
  (hordB : LengthAlgebra.KoszulFinite (NormalizedLength.ordinary T) (algebraMap B T ∘ z))
  (hspan : Ideal.span (Set.range (algebraMap A T ∘ a)) ≤
    (Ideal.span (Set.range (algebraMap B T ∘ z))).radical)
  (hres : Function.Surjective ((residue T).comp (algebraMap B T)))
  {I : Ideal D} (mu : NormalizedLength D I) (ι : R →+* D)
  (hfinite : ∀ i, mu.len (TorAlg ι i T) ≠ ⊤)
  (hlim : ∀ i, Tendsto (fun n ↦
    (Module.length B (TorModule B i (M n) T) : ℝ≥0∞) / (s n : ℝ≥0∞))
    atTop (𝓝 (mu.len (TorAlg ι i T))))

set_option maxHeartbeats 800000 in
-- 近似側・比較側の異なる支持部分圏と二つの長さ評価の型の比較に必要。
include ha hKos hc hdesc hτfin hτzero hτlim eK hB hv hM hordB hspan hres hfinite hlim in
/-- 有限近似の同じ複体から、第二比較の支持と全ひねりの評価・共役和等式を得る。 -/
theorem secondComparison_of_approximation :
    ∃ hT : paperSupportedRank (algebraMap A T ∘ a) ((paperSequenceFunctor T s).obj
      (sequenceHomotopyObj
        (((FreeSequence.changeRing (algebraMap B T)).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded (algebraMap B T) K hK))),
      (∀ g : G, paperRankEulerK0 (NormalizedLength.ordinary T) Submodule.fg_bot
        (algebraMap A T ∘ a) bot_le hord U hU hs
        (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj
          (sequenceHomotopyObj
            (((FreeSequence.changeRing (algebraMap B T)).mapHomologicalComplex (.up ℤ)).obj K)
            (changeRing_strictlyBounded (algebraMap B T) K hK)), hT⟩) = lambdaChi mu ι T) ∧
      (Fintype.card G : ℝ) * lambdaChi mu ι T =
        ∑ g : G, paperBaseChangeEulerK0 ψ (algebraMap A T ∘ a) lam hfg hJ hfin U hU hs
          (g • TriangulatedK0.mk ⟨(paperSequenceFunctor T s).obj
            (sequenceHomotopyObj
              (((FreeSequence.changeRing (algebraMap B T)).mapHomologicalComplex (.up ℤ)).obj K)
              (changeRing_strictlyBounded (algebraMap B T) K hK)), hT⟩) := by
  let L := ((FreeSequence.changeRing (algebraMap B T)).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded (algebraMap B T) K hK
  have hT := paperSupportedRank_of_span_le_radical (algebraMap B T ∘ z)
    (algebraMap A T ∘ a) hspan (paperChangedComplex_supported (algebraMap B T) z K hK hB)
  have hvalue : paperBaseChangeEulerK0 (algebraMap B T) z (NormalizedLength.ordinary T)
      Submodule.fg_bot bot_le hordB U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor B s).obj (sequenceHomotopyObj K hK), hB⟩) =
        lambdaChi mu ι T :=
    paperOrdinaryEulerK0_eq_of_common_residueField_limits M l hs τ hτfin hτzero hτlim
      K hK eK z hB v hv hM U hU hres hordB (fun i ↦ mu.len (TorAlg ι i T)) hfinite hlim
  have hvalueL := (paperBaseChangeEulerK0_complex_support_change (algebraMap B T) z
    (NormalizedLength.ordinary T) Submodule.fg_bot bot_le hordB U hU hs
    (algebraMap A T ∘ a) bot_le hord K hK hB hT).symm.trans hvalue
  refine ⟨hT, ?_, ?_⟩
  · intro g
    exact (paperOrdinaryEulerK0_smul U hU hs L hL a hord hT g).trans hvalueL
  · have he := secondComparison_of_baseChangedComplex ψ lam hfg a hJ hfin hord
      ha hKos U hU hs hc hdesc (algebraMap B T) z hordB K hK hB hT
    rwa [hvalue] at he

end SerrePositivity.Section5

end ApproximationSecondComparisonPart
