module

public import SerrePositivity.BhattScholze.PrincipalDPBaseChangeUniversal

/-! # 一元分冪表示環の実mod p比較

通常のp商を比較する。導来完備化や古典的完備化への置換は含まない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} [CommRing A]
variable (p : ℕ) (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "I₀" => Ideal.span {(p : A)}
local notation "Q₀" => A ⧸ I₀
local notation "bar₀" => Ideal.Quotient.mk I₀

/-- 係数のp主イデアルの実表示環への像は、表示環内のp主イデアル。 -/
theorem principalDPModP_coefficientIdeal_map :
    (I₀).map (algebraMap A R₀) = Ideal.span {(p : R₀)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 一元分冪表示環の実p商と、係数環のp商上の実表示環の標準環同型。 -/
def principalDPModPEquiv :
    (R₀ ⧸ Ideal.span {(p : R₀)}) ≃+* PrincipalDPPresentation Q₀ (bar₀ y) :=
  (Ideal.quotEquivOfEq (principalDPModP_coefficientIdeal_map p y).symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R₀ I₀).toRingEquiv.trans
      (principalDPBaseChangeUniversalEquiv (B := Q₀) y).toRingEquiv)

/-- 実mod p同型は、すべての標準生成元の商像を対応する標準生成元へ送る。 -/
theorem principalDPModPEquiv_generator (n : ℕ) :
    principalDPModPEquiv p y (Ideal.Quotient.mk _ (principalDPGenerator y n)) =
      principalDPGenerator (bar₀ y) n := by
  rw [principalDPModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk R₀ I₀ (principalDPGenerator y n)]
  change principalDPBaseChangeUniversalEquiv (B := Q₀) y
    ((1 : Q₀) ⊗ₜ[A] principalDPGenerator y n) = _
  rw [principalDPBaseChangeUniversalEquiv_tmul_generator, map_one, one_mul]
  rfl

/-- 実mod p同型は、元の環の全係数の商像を対応する係数へ送る。 -/
theorem principalDPModPEquiv_coeff (a : A) :
    principalDPModPEquiv p y (Ideal.Quotient.mk _ (algebraMap A R₀ a)) =
      algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)) (bar₀ a) := by
  rw [principalDPModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk R₀ I₀ (algebraMap A R₀ a)]
  change principalDPBaseChangeUniversalEquiv (B := Q₀) y
    ((1 : Q₀) ⊗ₜ[A] algebraMap A R₀ a) = _
  have ha : (1 : Q₀) ⊗ₜ[A] algebraMap A R₀ a = bar₀ a ⊗ₜ[A] (1 : R₀) := by
    change (1 : Q₀) ⊗ₜ[A] algebraMap A R₀ a = algebraMap A Q₀ a ⊗ₜ[A] (1 : R₀)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (TensorProduct.tmul_smul (R := A) a (1 : Q₀) (1 : R₀)).trans
      (TensorProduct.smul_tmul' a (1 : Q₀) (1 : R₀))
  rw [ha, principalDPBaseChangeUniversalEquiv_coeff]
  rfl

end SerrePositivity.BhattScholze
