module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPEnvelopeBaseChange
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 基底変更した実切断多項式環とB/(y^p)の同定 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialQuotientAlgebra
variable (p : ℕ) {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "y₀" => algebraMap P₀ B Polynomial.X
local notation "J₀" => Ideal.span {y₀ ^ p}
local notation "U₀" => RankOneDPBaseChangedTruncation p A B

/-- X^pの主イデアルの像は、指定した変数の像のp乗の主イデアル。 -/
theorem rankOneDPTruncationRelationIdeal_map :
    (Ideal.span {(Polynomial.X : P₀) ^ p}).map (algebraMap P₀ B) = J₀ := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

/-- 基底変更した実切断多項式環と、指定されたBの実商との環同型。 -/
def rankOneDPTruncationQuotientEquiv : B ⧸ J₀ ≃+* U₀ := by
  let I : Ideal P₀ := Ideal.span {(Polynomial.X : P₀) ^ p}
  have hI : I.map (algebraMap P₀ B) = J₀ := rankOneDPTruncationRelationIdeal_map p
  exact (Ideal.quotEquivOfEq hI.symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm P₀ B C₀).toRingEquiv)

/-- 実商の任意の代表元は、対応する標準純テンソルへ送られる。 -/
theorem rankOneDPTruncationQuotientEquiv_mk (b : B) :
    rankOneDPTruncationQuotientEquiv (A := A) p (Ideal.Quotient.mk J₀ b) =
      (1 : C₀) ⊗ₜ[P₀] b := by
  rfl

/-- 指定された変数の商像は、実切断多項式環の根の基底変更像へ送られる。 -/
theorem rankOneDPTruncationQuotientEquiv_variable :
    rankOneDPTruncationQuotientEquiv (A := A) (B := B) p (Ideal.Quotient.mk J₀ y₀) =
      AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ⊗ₜ[P₀] (1 : B) := by
  rw [rankOneDPTruncationQuotientEquiv_mk]
  have h := TensorProduct.smul_tmul (R := P₀) (Polynomial.X : P₀) (1 : C₀) (1 : B)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  exact h.symm

end SerrePositivity.BhattScholze
