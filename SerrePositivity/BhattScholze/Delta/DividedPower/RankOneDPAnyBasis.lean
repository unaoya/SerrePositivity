module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPBaseChangeUniversal
public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # 任意係数環上の既存一元分冪代数の実基底

整数係数の基底を無条件の実基底変更同型で移す。係数のpねじれを許す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze

/-- 任意の可換環上の既存一元分冪代数の、標準分冪による実基底。 -/
def rankOneDPAnyBasis (A : Type u) [CommRing A] :
    Module.Basis ℕ A (DividedPowerAlgebra A A) :=
  (((rankOneDPBasis (A := ℤ) ℚ Int.cast_injective).baseChange A).map
    (rankOneDPBaseChangeUniversalEquiv (A := ℤ) (B := A)).toLinearEquiv)

/-- 任意係数で構成した実基底の値は、元の標準生成元γ_n(1)。 -/
theorem rankOneDPAnyBasis_apply (A : Type u) [CommRing A] (n : ℕ) :
    rankOneDPAnyBasis A n = DividedPowerAlgebra.dp A n (1 : A) := by
  rw [rankOneDPAnyBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rankOneDPBasis_apply]
  exact rankOneDPBaseChangeMap_dp n

/-- 任意の可換係数環で、既存一元分冪代数は自由。 -/
theorem rankOneDPAny_moduleFree (A : Type u) [CommRing A] :
    Module.Free A (DividedPowerAlgebra A A) :=
  Module.Free.of_basis (rankOneDPAnyBasis A)

/-- 係数環の正則元は、任意係数の既存一元分冪代数上でも正則。 -/
theorem rankOneDPAny_isSMulRegular {A : Type u} [CommRing A] (r : A)
    (hr : IsSMulRegular A r) :
    IsSMulRegular (DividedPowerAlgebra A A) (algebraMap A (DividedPowerAlgebra A A) r) := by
  let : Module.Free A (DividedPowerAlgebra A A) := rankOneDPAny_moduleFree A
  exact hr.of_flat

end SerrePositivity.BhattScholze
