module

public import SerrePositivity.BhattScholze.RankOneDPEnvelopeBaseChange

/-! # 基底変更後の通常分冪添加環の自由性と忠実平坦性 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "DA" => DividedPowerAlgebra A A
local notation "U₀" => RankOneDPBaseChangedTruncation p A B
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 実比較射U→Dの作用に関する、基底変更後の実分冪基底。 -/
def rankOneDPEnvelopeBasis :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.Basis ℕ U₀ D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hprime.pos hp
  letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  exact ((rankOneDPTruncatedBlockBasis hprime hp).baseChange U₀).map
    (rankOneDPEnvelopeBaseChangeEquiv hprime.pos hp).toLinearEquiv

/-- 実U基底の各元は指定されたγ_(pk)⊗1。 -/
theorem rankOneDPEnvelopeBasis_apply (k : ℕ) :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    rankOneDPEnvelopeBasis hprime hp k =
      DividedPowerAlgebra.dp A (p * k) (1 : A) ⊗ₜ[P₀] (1 : B) := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hprime.pos hp
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  rw [rankOneDPEnvelopeBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rankOneDPTruncatedBlockBasis_apply]
  change rankOneDPEnvelopeTensorEquiv hprime.pos hp
    ((1 : U₀) ⊗ₜ[C₀] DividedPowerAlgebra.dp A (p * k) (1 : A)) = _
  rw [show (1 : U₀) = (1 : C₀) ⊗ₜ[P₀] (1 : B) from Algebra.TensorProduct.one_def,
    rankOneDPEnvelopeTensorEquiv_tmul, map_one, one_mul]

/-- 通常分冪添加環は指定されたU作用について自由。零環も含む。 -/
theorem rankOneDPEnvelope_moduleFree :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.Free U₀ D₀ := by
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  exact Module.Free.of_basis (rankOneDPEnvelopeBasis hprime hp)

/-- 通常分冪添加環は指定されたU作用について平坦。 -/
theorem rankOneDPEnvelope_moduleFlat :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.Flat U₀ D₀ := by
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Module.Free U₀ D₀ := rankOneDPEnvelope_moduleFree hprime hp
  infer_instance

/-- 通常分冪添加環は指定されたU作用について忠実平坦。零環も含む。 -/
theorem rankOneDPEnvelope_moduleFaithfullyFlat :
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
    Module.FaithfullyFlat U₀ D₀ := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hprime.pos hp
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Module.FaithfullyFlat C₀ DA := rankOneDPTruncated_moduleFaithfullyFlat hprime hp
  exact Module.FaithfullyFlat.of_linearEquiv U₀ (U₀ ⊗[C₀] DA)
    (rankOneDPEnvelopeBaseChangeEquiv hprime.pos hp).symm.toLinearEquiv

end SerrePositivity.BhattScholze
