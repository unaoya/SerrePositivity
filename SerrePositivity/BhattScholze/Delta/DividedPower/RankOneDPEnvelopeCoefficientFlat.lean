module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPQuotientToEnvelope

/-! # 通常分冪添加環の実係数射と係数環上の平坦性 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "DA" => DividedPowerAlgebra A A
local notation "Q₀" => B ⧸ Ideal.span {(algebraMap P₀ B Polynomial.X) ^ p}
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 指定された多項式作用から実商へ誘導される実係数射。 -/
def rankOneDPPowerQuotientCoefficientMap : A →+* Q₀ :=
  (Ideal.Quotient.mk _).comp ((algebraMap P₀ B).comp Polynomial.C)

/-- 分冪添加環の左成分を通じる実係数射。 -/
def rankOneDPEnvelopeCoefficientMap : A →+* D₀ :=
  (Algebra.TensorProduct.includeLeft (R := P₀) (S := P₀) (A := DA) (B := B)).toRingHom.comp
    (algebraMap A DA)

/-- 実商への係数射による具体的A代数構造。 -/
abbrev rankOneDPPowerQuotientCoefficientAlgebra : Algebra A Q₀ :=
  (rankOneDPPowerQuotientCoefficientMap (p := p) (A := A) (B := B)).toAlgebra

/-- 分冪添加環への係数射による具体的A代数構造。 -/
abbrev rankOneDPEnvelopeCoefficientAlgebra : Algebra A D₀ :=
  (rankOneDPEnvelopeCoefficientMap (A := A) (B := B)).toAlgebra

/-- 実商から分冪添加環への射は、指定した両実係数射と可換。 -/
theorem rankOneDPQuotientToEnvelope_comp_coefficient (hpos : 0 < p) (hp : (p : A) = 0) :
    (rankOneDPQuotientToEnvelope (B := B) hpos hp).comp
        rankOneDPPowerQuotientCoefficientMap =
      rankOneDPEnvelopeCoefficientMap := by
  apply RingHom.ext
  intro a
  change rankOneDPQuotientToEnvelope hpos hp
    (Ideal.Quotient.mk _ (algebraMap P₀ B (Polynomial.C a))) =
      (algebraMap A DA a) ⊗ₜ[P₀] (1 : B)
  rw [rankOneDPQuotientToEnvelope_mk]
  have h := TensorProduct.smul_tmul (R := P₀) (Polynomial.C a : P₀) (1 : DA) (1 : B)
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  change (rankOneDPPolynomialMap A (Polynomial.C a)) ⊗ₜ[P₀] (1 : B) =
    (1 : DA) ⊗ₜ[P₀] algebraMap P₀ B (Polynomial.C a) at h
  rw [rankOneDPPolynomialMap_C] at h
  exact h.symm

/-- 実商の平坦性を分冪添加環へ移すための、実係数スカラー塔。 -/
theorem rankOneDPEnvelopeCoefficient_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
    IsScalarTower A Q₀ D₀ := by
  let : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq (R := A) (S := Q₀) (A := D₀)
    (fun a ↦ (RingHom.congr_fun (rankOneDPQuotientToEnvelope_comp_coefficient hpos hp) a).symm)

/-- 実商B/(y^p)が係数環上平坦なら、通常分冪添加環も指定した係数作用について平坦。 -/
theorem rankOneDPEnvelope_flat_of_quotient_flat (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
    Module.Flat A Q₀ → Module.Flat A D₀ := by
  let : Algebra A Q₀ := rankOneDPPowerQuotientCoefficientAlgebra
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : IsScalarTower A Q₀ D₀ := rankOneDPEnvelopeCoefficient_isScalarTower hprime.pos hp
  intro hQ
  let := hQ
  let : Module.Flat Q₀ D₀ := rankOneDPQuotientToEnvelope_moduleFlat hprime hp
  exact Module.Flat.trans A Q₀ D₀

end SerrePositivity.BhattScholze
