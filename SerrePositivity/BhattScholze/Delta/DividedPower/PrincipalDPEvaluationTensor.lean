module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPEvaluatedEnvelope
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPPresentation
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # 一元分冪表示環と係数環への実評価テンソル環 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} [CommRing A]
attribute [local instance] rankOneDPPolynomialAlgebra
local notation "P₀" => Polynomial A
local notation "G₀" => DividedPowerAlgebra A A
local notation "I₀" y => Ideal.span {(Polynomial.X - Polynomial.C y : P₀)}

/-- 多項式一次商の既存同型を、指定した評価多項式作用に関する代数同型とする。 -/
def principalDPEvaluationPolynomialEquiv (y : A) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    (P₀ ⧸ I₀ y) ≃ₐ[P₀] A := by
  letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
  exact { (Polynomial.quotientSpanXSubCAlgEquiv y).toRingEquiv with
    commutes' := fun f ↦ by
      change Polynomial.eval y f = Polynomial.aeval y f
      simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] }

/-- 多項式一次関係の分冪代数への実像は、既存の表示関係イデアル。 -/
theorem principalDPEvaluation_relationIdeal (y : A) :
    (I₀ y).map (algebraMap P₀ G₀) = principalDPRelationIdeal y := by
  rw [Ideal.map_span, Set.image_singleton, map_sub]
  change Ideal.span {rankOneDPPolynomialMap A Polynomial.X -
    rankOneDPPolynomialMap A (Polynomial.C y)} = _
  rw [rankOneDPPolynomialMap_X, rankOneDPPolynomialMap_C]
  rfl

/-- 表示環から、Xをyへ評価した実テンソル環への標準同型。 -/
def principalDPEvaluationTensorEquiv (y : A) :
    PrincipalDPPresentation A y ≃+* RankOneDPEvaluatedEnvelope A A y := by
  letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
  exact (Ideal.quotEquivOfEq (principalDPEvaluation_relationIdeal y).symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot G₀ (I₀ y)).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : G₀ ≃ₐ[G₀] G₀)
        (principalDPEvaluationPolynomialEquiv y)).toRingEquiv)

/-- すべての分冪代数の商代表元は、その元と1の純テンソルへ写る。 -/
theorem principalDPEvaluationTensorEquiv_mk (y : A) (d : G₀) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    principalDPEvaluationTensorEquiv y (Ideal.Quotient.mk _ d) = d ⊗ₜ[P₀] (1 : A) := by
  let : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
  rw [principalDPEvaluationTensorEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk G₀ (I₀ y) d]
  simp only [AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- 全標準分冪生成元上の実評価テンソル比較式。 -/
theorem principalDPEvaluationTensorEquiv_generator (y : A) (n : ℕ) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    principalDPEvaluationTensorEquiv y (principalDPGenerator y n) =
      DividedPowerAlgebra.dp A n (1 : A) ⊗ₜ[P₀] (1 : A) :=
  principalDPEvaluationTensorEquiv_mk y _

/-- 全係数上の実評価テンソル比較式。 -/
theorem principalDPEvaluationTensorEquiv_coeff (y a : A) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    principalDPEvaluationTensorEquiv y (algebraMap A (PrincipalDPPresentation A y) a) =
      (algebraMap A G₀ a) ⊗ₜ[P₀] (1 : A) :=
  principalDPEvaluationTensorEquiv_mk y _

/-- 元の係数作用を保つ、表示環と実評価テンソル環のA代数同型。 -/
def principalDPEvaluationTensorAlgEquiv (y : A) :
    PrincipalDPPresentation A y ≃ₐ[A] RankOneDPEvaluatedEnvelope A A y :=
  { principalDPEvaluationTensorEquiv y with
    commutes' := fun a ↦ principalDPEvaluationTensorEquiv_coeff y a }

end SerrePositivity.BhattScholze
