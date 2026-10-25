module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPEnvelopeCoefficientFlat

/-! # 具体的A代数Bと元yへの通常分冪添加の評価入口

元の係数作用と商の自然な作用を保ったまま、通常の平坦性を移す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 元yへの既存aevalが指定する、Bへの具体的多項式作用。 -/
abbrev rankOneDPEvaluationAlgebra (y : B) : Algebra (Polynomial A) B :=
  (Polynomial.aeval y).toRingHom.toAlgebra

/-- 元の係数作用とyへの評価作用は実スカラー塔をなす。 -/
theorem rankOneDPEvaluation_isScalarTower (y : B) :
    letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
    IsScalarTower A (Polynomial A) B := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  exact IsScalarTower.of_algebraMap_eq (R := A) (S := Polynomial A) (A := B)
    (fun a ↦ (Polynomial.aeval y).commutes a |>.symm)

/-- Bの指定元yへの実評価作用で作った通常分冪添加テンソル環。 -/
abbrev RankOneDPEvaluatedEnvelope (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (y : B) :=
  letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  RankOneDPBaseChangedEnvelope A B

/-- 評価した多項式変数のp乗の商は、指定された元yのp乗の商と同じ実イデアルで定義される。 -/
theorem rankOneDPEvaluatedRelationIdeal (p : ℕ) (y : B) :
    letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
    Ideal.span {y ^ p} = Ideal.span {(algebraMap (Polynomial A) B Polynomial.X) ^ p} := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  change Ideal.span {y ^ p} = Ideal.span {(Polynomial.aeval y Polynomial.X) ^ p}
  rw [Polynomial.aeval_X]

variable {p : ℕ}

/-- 元yの実商から、評価した通常分冪添加環への具体的環射。 -/
def rankOneDPEvaluatedQuotientMap (hpos : 0 < p) (hp : (p : A) = 0) (y : B) :
    B ⧸ Ideal.span {y ^ p} →+* RankOneDPEvaluatedEnvelope A B y := by
  letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  exact (rankOneDPQuotientToEnvelope (B := B) hpos hp).comp
    (Ideal.quotEquivOfEq (rankOneDPEvaluatedRelationIdeal (A := A) p y)).toRingHom

/-- 評価した実環射は、すべての商代表元bを1⊗bへ送る。 -/
theorem rankOneDPEvaluatedQuotientMap_mk (hpos : 0 < p) (hp : (p : A) = 0) (y b : B) :
    letI : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
    rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ b) =
      (1 : DividedPowerAlgebra A A) ⊗ₜ[Polynomial A] b := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  change rankOneDPQuotientToEnvelope hpos hp (Ideal.Quotient.mk _ b) = _
  exact rankOneDPQuotientToEnvelope_mk hpos hp b

/-- 元yの実商からの指定された環射による具体的代数構造。 -/
abbrev rankOneDPEvaluatedQuotientAlgebra (hpos : 0 < p) (hp : (p : A) = 0) (y : B) :
    Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
  (rankOneDPEvaluatedQuotientMap hpos hp y).toAlgebra

/-- 元yの実商からの指定された環射は忠実平坦。零環も含む。 -/
theorem rankOneDPEvaluatedQuotient_moduleFaithfullyFlat
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B) :
    letI : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
      rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
    Module.FaithfullyFlat (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  let Q := B ⧸ Ideal.span {y ^ p}
  let Q' := B ⧸ Ideal.span {(algebraMap (Polynomial A) B Polynomial.X) ^ p}
  let D := RankOneDPEvaluatedEnvelope A B y
  let eQ : Q ≃+* Q' := Ideal.quotEquivOfEq (rankOneDPEvaluatedRelationIdeal (A := A) p y)
  let : Algebra Q Q' := eQ.toRingHom.toAlgebra
  let : Algebra Q' D := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : Algebra Q D := rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let : IsScalarTower Q Q' D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let e : Q ≃ₐ[Q] Q' := { __ := eQ, commutes' := fun _ ↦ rfl }
  let : Module.FaithfullyFlat Q Q' := Module.FaithfullyFlat.of_linearEquiv Q Q e.symm.toLinearEquiv
  let : Module.FaithfullyFlat Q' D := rankOneDPQuotientToEnvelope_moduleFaithfullyFlat hprime hp
  exact Module.FaithfullyFlat.trans Q Q' D

/-- 元のA作用、自然な商作用、指定した分冪添加作用の実スカラー塔。 -/
theorem rankOneDPEvaluatedQuotient_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) (y : B) :
    letI : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
      rankOneDPEvaluatedQuotientAlgebra hpos hp y
    IsScalarTower A (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  let : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotientAlgebra hpos hp y
  apply IsScalarTower.of_algebraMap_eq (R := A) (S := B ⧸ Ideal.span {y ^ p})
    (A := RankOneDPEvaluatedEnvelope A B y)
  intro a
  change (algebraMap A (DividedPowerAlgebra A A) a) ⊗ₜ[Polynomial A] (1 : B) =
    rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ (algebraMap A B a))
  rw [rankOneDPEvaluatedQuotientMap_mk]
  have h := TensorProduct.smul_tmul (R := Polynomial A) (Polynomial.C a : Polynomial A)
    (1 : DividedPowerAlgebra A A) (1 : B)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  change rankOneDPPolynomialMap A (Polynomial.C a) ⊗ₜ[Polynomial A] (1 : B) =
    (1 : DividedPowerAlgebra A A) ⊗ₜ[Polynomial A] Polynomial.aeval y (Polynomial.C a) at h
  rw [rankOneDPPolynomialMap_C, Polynomial.aeval_C] at h
  exact h

/-- 自然な商A加群B/(y^p)が平坦なら、元yへ評価した通常分冪添加環もA平坦。 -/
theorem rankOneDPEvaluatedEnvelope_flat_of_quotient_flat
    (hprime : p.Prime) (hp : (p : A) = 0) (y : B)
    (hQ : Module.Flat A (B ⧸ Ideal.span {y ^ p})) :
    Module.Flat A (RankOneDPEvaluatedEnvelope A B y) := by
  let : Algebra (Polynomial A) B := rankOneDPEvaluationAlgebra (A := A) y
  let : Algebra (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let : IsScalarTower A (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotient_isScalarTower hprime.pos hp y
  let := hQ
  let : Module.FaithfullyFlat (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y) :=
    rankOneDPEvaluatedQuotient_moduleFaithfullyFlat hprime hp y
  exact Module.Flat.trans A (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope A B y)

end SerrePositivity.BhattScholze
