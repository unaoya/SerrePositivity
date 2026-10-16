module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 一元分冪代数の標準テンソル基底変更射

任意係数上の比較射と生成元公式を、基底の構成から独立に定める。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 基底係数の拡大と既存分冪代数のmapから得られる実テンソル比較射。 -/
def rankOneDPBaseChangeMap :
    B ⊗[A] DividedPowerAlgebra A A →ₐ[B] DividedPowerAlgebra B B :=
  Algebra.TensorProduct.lift (Algebra.ofId B (DividedPowerAlgebra B B))
    (DividedPowerAlgebra.map B (Algebra.linearMap A B)) (fun _ _ ↦ Commute.all _ _)

/-- 実比較射のすべての純テンソル上の式。 -/
theorem rankOneDPBaseChangeMap_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeMap (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

/-- 標準分冪基底の純テンソルは拡大後の標準分冪基底へ写る。 -/
theorem rankOneDPBaseChangeMap_dp (n : ℕ) :
    rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp B n (1 : B) := by
  rw [rankOneDPBaseChangeMap_tmul, map_one, one_mul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one]

end SerrePositivity.BhattScholze
