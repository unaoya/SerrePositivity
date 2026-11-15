module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：一つの変数を1に評価し、Proj の一標準開の次数零局所化から多項式環への全射を作る。
方針：通常の局所化への写像を評価へ延長し、斉次分数の値と変数・定数の原像を計算する。
規約：標準開と多項式環の全同型に先立ち、必要な向きの全射を供給する。
使われ方：C05 の多項式 affine の固有な Proj の周辺への immersion。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) (ι : Type u) [CommRing R]

/-- none 変数を1、some i を変数 i に送る実際の評価。 -/
def polynomialChartEvaluation : MvPolynomial (Option ι) R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ i.elim 1 MvPolynomial.X)

/-- 一標準開の次数零斉次局所化から多項式環への評価。 -/
def homogeneousPolynomialChartEvaluation :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Option ι) R)
      (MvPolynomial.X none) →+* MvPolynomial ι R :=
  (Localization.awayLift (polynomialChartEvaluation R ι) (MvPolynomial.X none)
    (by simp [polynomialChartEvaluation])).comp
      (algebraMap _ (Localization.Away (MvPolynomial.X (R := R) (none : Option ι))))

/-- none 変数の冪を分母とする斉次分数の評価は分子の評価。 -/
theorem homogeneousPolynomialChartEvaluation_mk (n : ℕ)
    (m : MvPolynomial (Option ι) R)
    (hm : m ∈ MvPolynomial.homogeneousSubmodule (Option ι) R (n • 1)) :
    homogeneousPolynomialChartEvaluation R ι
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R none) n m hm) =
        polynomialChartEvaluation R ι m := by
  change Localization.awayLift (polynomialChartEvaluation R ι) (MvPolynomial.X none)
      (by simp [polynomialChartEvaluation])
      (HomogeneousLocalization.val (HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (Option ι) R)
        (MvPolynomial.isHomogeneous_X R none) n m hm)) = _
  rw [HomogeneousLocalization.Away.val_mk]
  simpa only [one_pow, mul_one] using Localization.awayLift_mk
    (polynomialChartEvaluation R ι) (MvPolynomial.X none) m 1
    (by simp [polynomialChartEvaluation]) n

/-- 標準開の次数零局所化の評価は全射。 -/
theorem homogeneousPolynomialChartEvaluation_surjective :
    Function.Surjective (homogeneousPolynomialChartEvaluation R ι) := by
  intro q
  induction q using MvPolynomial.induction_on with
  | C r =>
      refine ⟨HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R none)
        0 (MvPolynomial.C r) (by simpa using MvPolynomial.isHomogeneous_C (Option ι) r), ?_⟩
      rw [homogeneousPolynomialChartEvaluation_mk]
      simp [polynomialChartEvaluation]
  | add q r hq hr =>
      obtain ⟨x, hx⟩ := hq
      obtain ⟨y, hy⟩ := hr
      exact ⟨x + y, by simp [hx, hy]⟩
  | mul_X q i hq =>
      obtain ⟨x, hx⟩ := hq
      let y := HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (Option ι) R) (MvPolynomial.isHomogeneous_X R none)
        1 (MvPolynomial.X (some i)) (by simpa using MvPolynomial.isHomogeneous_X R (some i))
      have hy : homogeneousPolynomialChartEvaluation R ι y = MvPolynomial.X i := by
        dsimp only [y]
        rw [homogeneousPolynomialChartEvaluation_mk]
        simp [polynomialChartEvaluation]
      exact ⟨x * y, by simp [hx, hy]⟩

/-- 次数零の係数の射と標準開の評価は、指定した定数多項式を保つ。 -/
theorem homogeneousPolynomialChartEvaluation_fromZero (r : R) :
    homogeneousPolynomialChartEvaluation R ι
      (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Option ι) R) (.powers (MvPolynomial.X none))
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Option ι) r⟩) = MvPolynomial.C r := by
  change homogeneousPolynomialChartEvaluation R ι
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R none)
        0 (MvPolynomial.C r) (by simpa using MvPolynomial.isHomogeneous_C (Option ι) r)) = _
  rw [homogeneousPolynomialChartEvaluation_mk]
  simp [polynomialChartEvaluation]

end SerrePositivity.AlgebraicGeometry
