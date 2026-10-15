module

public import SerrePositivity.BhattScholze.RankOneDPPolynomialAction
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 通常一元分冪添加環への実テンソル基底変更

Bへの多項式作用はAlgebra (Polynomial A) Bとして指定する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "DA" => DividedPowerAlgebra A A

/-- 指定された多項式作用に沿って実切断多項式環を基底変更した環。 -/
abbrev RankOneDPBaseChangedTruncation (p : ℕ) (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (Polynomial A) B] :=
  AdjoinRoot ((Polynomial.X : Polynomial A) ^ p) ⊗[Polynomial A] B

/-- 指定された多項式作用に沿う、通常の実一元分冪添加テンソル環。 -/
abbrev RankOneDPBaseChangedEnvelope (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra (Polynomial A) B] :=
  DividedPowerAlgebra A A ⊗[Polynomial A] B

local notation "U₀" => RankOneDPBaseChangedTruncation p A B
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 実切断多項式作用の基底変更で与えられる、UからDへの実比較射。 -/
def rankOneDPEnvelopeBaseChangeMap (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    U₀ →ₐ[C₀] D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact Algebra.TensorProduct.map (Algebra.ofId C₀ DA) (AlgHom.id P₀ B)

/-- 実比較射の全純テンソル上の具体式。 -/
theorem rankOneDPEnvelopeBaseChangeMap_tmul (hpos : 0 < p) (hp : (p : A) = 0) (c : C₀) (b : B) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    rankOneDPEnvelopeBaseChangeMap hpos hp (c ⊗ₜ[P₀] b) =
      rankOneDPTruncatedMap hpos hp c ⊗ₜ[P₀] b := by
  rfl

/-- 通常分冪添加環は、切断多項式環上の自由加群をUへ基底変更した実環に同型。 -/
def rankOneDPEnvelopeTensorEquiv (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    U₀ ⊗[C₀] DA ≃ₐ[C₀] D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact (Algebra.TensorProduct.comm C₀ U₀ DA).trans
    (Algebra.TensorProduct.cancelBaseChange P₀ C₀ C₀ DA B)

/-- 実基底変更同型の全生成純テンソル上の式。 -/
theorem rankOneDPEnvelopeTensorEquiv_tmul (hpos : 0 < p) (hp : (p : A) = 0)
    (c : C₀) (b : B) (t : DA) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    rankOneDPEnvelopeTensorEquiv hpos hp ((c ⊗ₜ[P₀] b) ⊗ₜ[C₀] t) =
      (rankOneDPTruncatedMap hpos hp c * t) ⊗ₜ[P₀] b := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  rw [rankOneDPEnvelopeTensorEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
  rfl

/-- 実同型はUの標準射を、指定された実比較射へ送る。 -/
theorem rankOneDPEnvelopeTensorEquiv_comp_includeLeft (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    (rankOneDPEnvelopeTensorEquiv hpos hp).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (R := C₀) (A := U₀) (B := DA)) =
      rankOneDPEnvelopeBaseChangeMap hpos hp := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  apply Algebra.TensorProduct.ext'
  intro c b
  change rankOneDPEnvelopeTensorEquiv hpos hp ((c ⊗ₜ[P₀] b) ⊗ₜ[C₀] (1 : DA)) = _
  rw [rankOneDPEnvelopeTensorEquiv_tmul, rankOneDPEnvelopeBaseChangeMap_tmul, mul_one]

/-- 実比較射U→Dによる具体的U代数構造。 -/
abbrev rankOneDPEnvelopeBaseChangedAlgebra (hpos : 0 < p) (hp : (p : A) = 0) : Algebra U₀ D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact (rankOneDPEnvelopeBaseChangeMap (B := B) hpos hp).toRingHom.toAlgebra

/-- 実比較射によるU作用を保つ、実U代数同型。 -/
def rankOneDPEnvelopeBaseChangeEquiv (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
    letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
    U₀ ⊗[C₀] DA ≃ₐ[U₀] D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
  exact
    { __ := (rankOneDPEnvelopeTensorEquiv hpos hp).toRingEquiv
      commutes' := fun u ↦
        DFunLike.congr_fun (rankOneDPEnvelopeTensorEquiv_comp_includeLeft hpos hp) u }

end SerrePositivity.BhattScholze
