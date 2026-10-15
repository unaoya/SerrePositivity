module

public import SerrePositivity.BhattScholze.PrincipalDPEvaluationTensor

/-! # 標数pでの一元分冪表示環の通常の忠実平坦性 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra
variable {p : ℕ} {B : Type v} [CommRing B]

/-- 指定した元のp乗商から、一元分冪表示環への実環射。 -/
def principalDPQuotientMap (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    B ⧸ Ideal.span {y ^ p} →+* PrincipalDPPresentation B y :=
  (principalDPEvaluationTensorEquiv y).symm.toRingHom.comp
    (rankOneDPEvaluatedQuotientMap hpos hp y)

/-- 実商射は、全代表元を自然な表示環の係数へ送る。 -/
theorem principalDPQuotientMap_mk (hpos : 0 < p) (hp : (p : B) = 0) (y b : B) :
    principalDPQuotientMap hpos hp y (Ideal.Quotient.mk _ b) =
      algebraMap B (PrincipalDPPresentation B y) b := by
  apply (principalDPEvaluationTensorEquiv y).injective
  change principalDPEvaluationTensorEquiv y
    ((principalDPEvaluationTensorEquiv y).symm
      (rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ b))) = _
  rw [RingEquiv.apply_symm_apply]
  change rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ b) =
    principalDPEvaluationTensorAlgEquiv y (algebraMap B (PrincipalDPPresentation B y) b)
  rw [(principalDPEvaluationTensorAlgEquiv y).commutes]
  let := rankOneDPEvaluatedQuotientAlgebra hpos hp y
  let := rankOneDPEvaluatedQuotient_isScalarTower hpos hp y
  change algebraMap (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope B B y)
    (algebraMap B (B ⧸ Ideal.span {y ^ p}) b) = _
  exact (IsScalarTower.algebraMap_apply B (B ⧸ Ideal.span {y ^ p})
    (RankOneDPEvaluatedEnvelope B B y) b).symm

/-- 実商射が指定する表示環の商上の代数構造。 -/
abbrev principalDPQuotientAlgebra (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    Algebra (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) :=
  (principalDPQuotientMap hpos hp y).toAlgebra

/-- 実評価テンソル同型は、指定したp乗商上の代数同型でもある。 -/
def principalDPQuotientTensorAlgEquiv (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hpos hp y
    letI := rankOneDPEvaluatedQuotientAlgebra hpos hp y
    PrincipalDPPresentation B y ≃ₐ[B ⧸ Ideal.span {y ^ p}]
      RankOneDPEvaluatedEnvelope B B y := by
  letI := principalDPQuotientAlgebra hpos hp y
  letI := rankOneDPEvaluatedQuotientAlgebra hpos hp y
  exact { principalDPEvaluationTensorEquiv y with
    commutes' := fun q ↦ (principalDPEvaluationTensorEquiv y).apply_symm_apply _ }

/-- 標数pの任意の一元入力の表示環は、その元のp乗商上で忠実平坦。 -/
theorem principalDPQuotient_moduleFaithfullyFlat
    (hprime : p.Prime) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hprime.pos hp y
    Module.FaithfullyFlat (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let := rankOneDPEvaluatedQuotient_moduleFaithfullyFlat hprime hp y
  exact Module.FaithfullyFlat.of_linearEquiv (B ⧸ Ideal.span {y ^ p})
    (RankOneDPEvaluatedEnvelope B B y)
    (principalDPQuotientTensorAlgEquiv hprime.pos hp y).toLinearEquiv

/-- 元のB係数作用と実p乗商作用は、表示環上でスカラー塔をなす。 -/
theorem principalDPQuotient_isScalarTower (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hpos hp y
    IsScalarTower B (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hpos hp y
  apply IsScalarTower.of_algebraMap_eq (R := B) (S := B ⧸ Ideal.span {y ^ p})
    (A := PrincipalDPPresentation B y)
  intro b
  exact (principalDPQuotientMap_mk hpos hp y b).symm

variable {A : Type u} [CommRing A] [Algebra A B]

/-- 任意の基底環Aの元の係数作用とも、実p乗商作用は整合する。 -/
theorem principalDPQuotient_isScalarTower_base
    (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hpos hp y
    IsScalarTower A (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hpos hp y
  apply IsScalarTower.of_algebraMap_eq (R := A) (S := B ⧸ Ideal.span {y ^ p})
    (A := PrincipalDPPresentation B y)
  intro a
  rw [IsScalarTower.algebraMap_apply A B (B ⧸ Ideal.span {y ^ p})]
  change algebraMap A (PrincipalDPPresentation B y) a =
    principalDPQuotientMap hpos hp y (Ideal.Quotient.mk _ (algebraMap A B a))
  rw [principalDPQuotientMap_mk, IsScalarTower.algebraMap_apply A B
    (PrincipalDPPresentation B y)]

/-- 標数pのBと任意の基底環Aに対し、自然な商B/(y^p)がA平坦なら表示環もA平坦。 -/
theorem principalDPPresentation_flat_of_quotient_flat
    (hprime : p.Prime) (hp : (p : B) = 0) (y : B)
    (hQ : Module.Flat A (B ⧸ Ideal.span {y ^ p})) :
    Module.Flat A (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := principalDPQuotient_isScalarTower_base (A := A) hprime.pos hp y
  let := principalDPQuotient_moduleFaithfullyFlat hprime hp y
  let := hQ
  exact Module.Flat.trans A (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y)

end SerrePositivity.BhattScholze
