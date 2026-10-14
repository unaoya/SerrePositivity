module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import SerrePositivity.CommutativeAlgebra.FractionDifferential
public import SerrePositivity.CommutativeAlgebra.CompletedRelativeDifferential

/-! # 有限整域拡大の完備相対微分を分数体へ移す

有限な相対微分の完備性を実際に確認し、通常微分の局所化同型へ接続する。
係数体上の絶対微分の完備化との比較は別の課題。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable (A D K L : Type*) [CommRing A] [CommRing D]
  [Field K] [Field L] [Algebra A D] [Algebra.EssFiniteType A D]
  [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
  [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L]
  [IsNoetherianRing D] [IsLocalRing D]
  (I : Ideal D) (hI : I ≤ IsLocalRing.maximalIdeal D) [IsAdicComplete I D]

/-- 完備相対微分の生成点での評価は、同じ分数体拡大の通常相対微分。 -/
def completedFractionDifferentialEquiv :
    L ⊗[D] AdicCompletion I (KaehlerDifferential A D) ≃ₗ[L]
      KaehlerDifferential K L :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
    (relativeDifferentialCompletionEquiv (R := A) I hI).symm).trans
      (fractionDifferentialEquiv A D K L)

@[simp] theorem completedFractionDifferentialEquiv_tmul_of_D (l : L) (d : D) :
    completedFractionDifferentialEquiv A D K L I hI
      (l ⊗ₜ[D] AdicCompletion.of I (KaehlerDifferential A D) (KaehlerDifferential.D A D d)) =
        l • KaehlerDifferential.D K L (algebraMap D L d) := by
  simp [completedFractionDifferentialEquiv]

omit [Algebra.EssFiniteType A D] in
include hI in
/-- 完備相対微分の生成点での次元0による分離性判定。
有限次元性は有限な整域拡大と有限な相対微分から供給する。 -/
theorem isSeparable_fractionRing_iff_finrank_completedRelativeDifferential_eq_zero
    [IsDomain A] [IsDomain D] [Module.Finite A D] :
    Algebra.IsSeparable K L ↔
      Module.finrank L (L ⊗[D] AdicCompletion I (KaehlerDifferential A D)) = 0 := by
  let : Module.Finite K L := finiteDimensional_fractionRing_of_finite A D K L
  rw [isSeparable_iff_finrank_kaehlerDifferential_eq_zero,
    ← (completedFractionDifferentialEquiv A D K L I hI).finrank_eq]

end SerrePositivity
