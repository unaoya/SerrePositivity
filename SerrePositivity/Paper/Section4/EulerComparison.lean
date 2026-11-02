module

public import SerrePositivity.Asymptotic.UniformLift
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.Paper.Section4.RankQuotient
public import SerrePositivity.LengthAlgebra.KoszulFormula

/-! # 論文の台つき圏の K₀ での Euler 比較（論文 Proposition 4.5）

## 概要

極大イデアルを生成する列の Koszul 完全性から台つきランク商の冪等完備性を得て（A 側の一様自由代表）、有限版の任意の Koszul Euler 数による公式から、論文の台つき圏の全対象についての基底公式を得る。通常・正規化の階数倍公式はその係数を具体的に計算した特殊例である。

## 使われ方

`SymmetricComparison`、Paper/Section5。
-/

@[expose] public noncomputable section

universe u

section UniformRepresentativePart

namespace SerrePositivity.Section4

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents IsLocalRing
open SerrePositivity.Asymptotic

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
  {s : ℕ → ℕ}

include hz hKoszul in
/-- A 側の支持つきランク商は、Koszul 完全性の下で冪等完備。 -/
theorem supportedRank_isIdempotentComplete_of_koszul :
    IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z) := by
  have hres : IsResolutionOf (koszulComplex z) (ModuleCat.of A (A ⧸ maximalIdeal A)) := by
    have h := isResolutionOf_koszul z hKoszul
    rw [hz] at h
    exact h
  have := isArtinianRing_quotient_span_of_eq hz
  exact supportedRank_isIdempotentComplete z (koszulComplex z) hres
    (fun i ↦ (koszulComplex_free_finite_X z i).1)
    (fun i ↦ (koszulComplex_free_finite_X z i).2) e (koszulComplex_isZero_X_of_lt z)
    (Ideal.span (Set.range z)).fg_of_isNoetherianRing
    (fun v _ q ↦ ordinary_koszul_pow_finite z v q)

end SerrePositivity.Section4

end UniformRepresentativePart

section PaperK0ComparisonPart

namespace SerrePositivity.Section4

open CategoryTheory CategoryTheory.Idempotents IsLocalRing Filter

set_option synthInstance.maxSize 2048
open SerrePositivity.Asymptotic

/-- 冪等完備化した論文の支持圏の K₀ 上の通常の Euler 評価。 -/
noncomputable def ordinaryPaperEulerK0
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (hArt : IsArtinianRing (R ⧸ Ideal.span (Set.range z)))
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+ ℝ := by
  letI := hArt
  exact paperRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot z bot_le
    (fun v _ i ↦ ordinary_koszul_pow_finite z v i) U hU hs

/-- 任意の Koszul Euler 数による、ランク商の全対象の基底公式。
係数代数の高次 Koszul 消滅や有限ランクは仮定しない。 -/
theorem koszulPaperEulerK0_changeRing
    {A C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] [CommRing C] [Nontrivial C]
    (φ : A →+* C) {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
    {e : ℕ} (z : Fin e → A)
    (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfin : LengthAlgebra.KoszulFinite lam (φ ∘ z))
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n) :
    (paperRankEulerK0 lam hfg (φ ∘ z) hJ hfin U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing φ z)) =
      LengthAlgebra.koszulEuler lam (φ ∘ z) •
        ordinaryPaperEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs := by
  have := supportedRank_isIdempotentComplete_of_koszul (s := s) z hz hKoszul
  dsimp only [ordinaryPaperEulerK0]
  apply paperRankEulerK0_changeRing
  intro P hP
  simpa only [← chiOrd_eq_lambdaEuler_ordinary] using
    LengthAlgebra.lambdaEuler_baseChange_eq_koszulEuler_mul φ lam hfg z hJ hfin hz hKoszul P hP

end SerrePositivity.Section4

end PaperK0ComparisonPart
