module

public import SerrePositivity.Paper.Section5.SecondComparison
public import SerrePositivity.Paper.Section5.ApproximationEuler

/-! # 同じ有限近似から支持の変更と第二比較を導く

有限近似の Tor 極限を通常評価と同定し、正則基底のパラメータへの支持変更を行う。
実際の K₀ 上の群作用について、すべての通常評価が同じ `lambdaChi` になり、
第二比較が成立する。近似先の写像を `twistedAlgebraMap` とすると本文の `c_σ` になる。
群が作用する環と、近似する長さ付き代数の長さとの同変性は要求しない。
-/

@[expose] public section

universe u

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
