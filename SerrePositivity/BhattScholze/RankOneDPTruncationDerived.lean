module

public import SerrePositivity.BhattScholze.RankOneDPEvaluatedEnvelope
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import Mathlib.Algebra.Polynomial.Monic

/-! # 切断多項式商の実導来係数拡大とKoszul比較

完備化は行わない。一般の評価代数を通常の商へ置換する主張は含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A

/-- 切断多項式を定めるX^pは、零環を含む任意係数多項式環で正則。 -/
theorem rankOneDPTruncationPolynomial_regular (p : ℕ) :
    IsSMulRegular P₀ ((Polynomial.X : P₀) ^ p) :=
  ((Polynomial.monic_X (R := A)).pow p).isRegular.left

/-- 切断多項式商への実導来係数拡大は、元の多項式環上で実Koszul coneと一致する。 -/
def rankOneDPTruncationDerivedKoszulIso (p : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    ((boundedAboveDerivedRestrictScalars
      (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj
      ((boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj X)).obj ≅
      (DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj :=
  restrictedDerivedQuotientKoszulIso _ (rankOneDPTruncationPolynomial_regular p) X

variable {B : Type u} [CommRing B] [Algebra A B]

/-- 実評価作用で、多項式X^pの像は指定した元のp乗。 -/
theorem rankOneDPTruncationEvaluation_power (p : ℕ) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    algebraMap P₀ B ((Polynomial.X : P₀) ^ p) = y ^ p := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  change Polynomial.aeval y ((Polynomial.X : P₀) ^ p) = _
  rw [map_pow, Polynomial.aeval_X]

/-- 評価加群上でのX^pの正則性は、元のB上でのy^pの正則性そのもの。 -/
theorem rankOneDPTruncationEvaluation_regular_iff (p : ℕ) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    IsSMulRegular B ((Polynomial.X : P₀) ^ p) ↔ IsSMulRegular B (y ^ p) := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  change Function.Injective (fun b : B ↦ ((Polynomial.X : P₀) ^ p) • b) ↔ _
  simp only [Algebra.smul_def, rankOneDPTruncationEvaluation_power]
  rfl

/-- 具体的評価代数Bの次数零対象に対する、切断多項式商の実導来Koszul比較。 -/
def rankOneDPTruncationEvaluationDerivedKoszulIso (p : ℕ) (y : B) :
    letI := rankOneDPEvaluationAlgebra (A := A) y
    let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B)
    ((boundedAboveDerivedRestrictScalars
      (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj
      ((boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : P₀) ^ p)}))).obj X)).obj ≅
      (DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj := by
  let := rankOneDPEvaluationAlgebra (A := A) y
  exact rankOneDPTruncationDerivedKoszulIso p
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ B))

end SerrePositivity.BhattScholze
