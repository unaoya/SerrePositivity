module

public import SerrePositivity.Paper.Section4.UniformRepresentative
public import SerrePositivity.Asymptotic.PaperBaseChange
public import SerrePositivity.LengthAlgebra.KoszulFormula

/-! # 論文の圏の K₀ 上での命題4.5

有限版の任意の Koszul Euler 数による公式と A 側の一様代表から、全対象の基底公式を得る。
通常・正規化の階数倍公式は、その係数を具体的に計算した特殊例である。
-/

@[expose] public section

universe u

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
