module

public import SerrePositivity.CommutativeAlgebra.FractionRingBasis
public import SerrePositivity.RingTheory.Kaehler
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.Field

/-! # 相対微分の分数体への局所化と分離性

概要：整域の拡大 `A → D` の分数体 `K`、`L` について、`L ⊗_D Ω_{D/A} ≅ Ω_{L/K}`（`fractionDifferentialEquiv`）。
`D/A` が有限なら、`L/K` が分離的であることと `L ⊗_D Ω_{D/A}` の次元が零であることは同値。
方針：局所化は形式エタールなので Mathlib の `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` と、
底の形式不分岐な拡大で相対微分が変わらないこと（`RingTheory/Kaehler`）を合成する。分離性は有限体拡大の判定へ渡す。
規約：分数体の間の代数構造は型クラスの引数で受け取る。`FractionRing A → FractionRing D` には Mathlib の
`FractionRing.liftAlgebra` を局所インスタンスとして使う。
使われ方：Cohen–Gabber の分離性（`CohenGabberNormalization`）、中間係数体上の完備微分の比較（`CofiniteNormalization`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct

section Fractions
variable (A D K L : Type*) [CommRing A] [CommRing D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra D L] [IsFractionRing D L] [Algebra A L] [Algebra K L]
  [IsScalarTower A D L] [IsScalarTower A K L]

/-- 環の通常相対微分を分数体へ局所化し、底環も分数体に移す自然な同型。 -/
def fractionDifferentialEquiv :
    L ⊗[D] KaehlerDifferential A D ≃ₗ[L] KaehlerDifferential K L := by
  let : Algebra.FormallyEtale D L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors D)
  let : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A D L).trans
    (relativeDifferentialEquivOfFormallyUnramified A K L)

@[simp] theorem fractionDifferentialEquiv_tmul_D (l : L) (d : D) :
    fractionDifferentialEquiv A D K L (l ⊗ₜ[D] KaehlerDifferential.D A D d) =
      l • KaehlerDifferential.D K L (algebraMap D L d) := by
  simp [fractionDifferentialEquiv, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D]
end Fractions

/-- 有限整域拡大の同じ分数体作用について、局所化した相対微分の次元で分離性を判定する。 -/
theorem isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero
    (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
    [Field K] [Field L] [Algebra A D] [Module.Finite A D]
    [Algebra A K] [IsFractionRing A K] [Algebra D L] [IsFractionRing D L]
    [Algebra A L] [Algebra K L] [IsScalarTower A D L] [IsScalarTower A K L] :
    Algebra.IsSeparable K L ↔ Module.finrank L (L ⊗[D] KaehlerDifferential A D) = 0 := by
  let : Module.Finite K L := finiteDimensional_fractionRing_of_finite A D K L
  rw [isSeparable_iff_finrank_kaehlerDifferential_eq_zero,
    ← (fractionDifferentialEquiv A D K L).finrank_eq]

attribute [local instance] FractionRing.liftAlgebra in
/-- 有限な整域拡大 `A ⊆ D` について、分数体の拡大（Mathlib の `FractionRing.liftAlgebra`）が分離的であることと、
局所化した相対微分 `Frac D ⊗_D Ω_{D/A}` の次元が零であることは同値。 -/
theorem isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero'
    (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D] [Algebra A D]
    [FaithfulSMul A D] [Module.Finite A D] :
    Algebra.IsSeparable (FractionRing A) (FractionRing D) ↔
      Module.finrank (FractionRing D) (FractionRing D ⊗[D] KaehlerDifferential A D) = 0 :=
  isSeparable_fractionRing_iff_finrank_tensorDifferential_eq_zero A D
    (FractionRing A) (FractionRing D)

end SerrePositivity
