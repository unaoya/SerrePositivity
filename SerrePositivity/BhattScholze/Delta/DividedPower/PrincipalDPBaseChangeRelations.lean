module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPBaseChangeMap
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPPresentation
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 一元分冪表示の関係式と標準基底変更射

係数環の正則性を仮定せず、標準比較射が一次関係を保つことを示す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 実一元分冪基底変更射は、指定された表示関係を対応する関係へ送る。 -/
theorem rankOneDPBaseChangeMap_relation (y : A) :
    rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A]
      (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A (DividedPowerAlgebra A A) y)) =
      DividedPowerAlgebra.dp B 1 (1 : B) -
        algebraMap B (DividedPowerAlgebra B B) (algebraMap A B y) := by
  rw [TensorProduct.tmul_sub, map_sub, rankOneDPBaseChangeMap_dp,
    rankOneDPBaseChangeMap_tmul, map_one, one_mul]
  exact congrArg (fun t ↦ DividedPowerAlgebra.dp B 1 (1 : B) - t)
    ((DividedPowerAlgebra.map B (Algebra.linearMap A B)).commutes y)

end SerrePositivity.BhattScholze
