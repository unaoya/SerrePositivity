module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPIntegral

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential

/-!
# pd 偏微分と係数変換

## 概要
未完備 pd 模型の座標偏微分は基底環の射に沿う係数変換と可換。

## 方針
多項式単項式と分冪単項式のテンソル基底で照合する。

## 規約
第 0 頂点の変数と頂点の差の分冪を別々に扱う。

## 使われ方
pd de Rham 双複体の mod p 還元。
-/

public noncomputable section

open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r n : ℕ)

private def rawCoeffLinear : pdRaw A r n →ₛₗ[algebraMap A B] pdRaw B r n where
  toAddHom := (pdRawCoefficients A B r n).toAddMonoidHom
  map_smul' a x := by
    change pdRawCoefficients A B r n (a • x) =
      (algebraMap A B a) • pdRawCoefficients A B r n x
    have h := (pdRawCoefficients A B r n).toLinearMap.map_smul a x
    exact h.trans (algebraMap_smul B a _).symm

set_option backward.isDefEq.respectTransparency false in
/-- 多項式座標と分冪座標の偏微分は係数変換と可換。 -/
theorem pdRawPartial_coefficients (a : pdCoordinates r n) (x : pdRaw A r n) :
    pdRawCoefficients A B r n (pdRawPartial A r n a x) =
      pdRawPartial B r n a (pdRawCoefficients A B r n x) := by
  let f := rawCoeffLinear A B r n
  suffices e : f.comp (pdRawPartial A r n a) = (pdRawPartial B r n a).comp f from
    DFunLike.congr_fun e x
  apply (pdRawBasis A r n).ext
  rintro ⟨m, j⟩
  change pdRawCoefficients A B r n (pdRawPartial A r n a (pdRawBasis A r n (m,j))) =
    pdRawPartial B r n a (pdRawCoefficients A B r n (pdRawBasis A r n (m,j)))
  rw [pdRawCoefficients_basis]
  have h (R : Type u) [CommRing R] : pdRawBasis R r n (m,j) =
      MvPolynomial.monomial m 1 ⊗ₜ[R] freeDPMonomial _ R j := by
    rw [pdRawBasis, Module.Basis.tensorProduct_apply', freeDPBasis_apply]
    rfl
  rw [h A, h B]
  rcases a with t | t
  · simp only [partial_inl_tmul, pdRawCoefficients_tmul, MvPolynomial.pderiv_monomial,
      MvPolynomial.map_monomial, map_mul, map_one, map_natCast]
    have hj := freeDPBaseChangeMap_monomial (Fin r × Fin n) A B j
    change algebraMap B _ 1 * DividedPowerAlgebra.map B (freeDPCoefficientMap _ A B)
      (freeDPMonomial _ A j) = _ at hj
    rw [map_one, one_mul] at hj
    rw [hj]
  · by_cases hz : j t = 0
    · simp [partial_inr_tmul, freeDPPartial_monomial, hz]
    · simp only [partial_inr_tmul, freeDPPartial_monomial, hz, ite_false, pdRawCoefficients_tmul,
        MvPolynomial.map_monomial, map_one]
      have hj := freeDPBaseChangeMap_monomial (Fin r × Fin n) A B (j - Finsupp.single t 1)
      change algebraMap B _ 1 * DividedPowerAlgebra.map B (freeDPCoefficientMap _ A B)
        (freeDPMonomial _ A _) = _ at hj
      rw [map_one, one_mul] at hj
      rw [hj]

end SerrePositivity.BhattScholze.Prismatic
