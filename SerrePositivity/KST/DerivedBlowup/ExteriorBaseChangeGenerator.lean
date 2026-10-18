module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeMap
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
概要：KST Def3.1 の Koszul 外積模型の係数変更に使う生成元写像。
方針：S⊗M から S⊗Λ(M) への写像が平方零であることを tensor 帰納法で示す。
規約：2の可逆性を仮定しない。一般 Clifford 基底変更定理は使わない。
使われ方：任意可換環上の外積代数のスカラー拡大比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：係数変更後の生成元を元の外積代数の tensor へ送る。
方針：S 側の恒等写像と外積の生成元包含を tensor する。
規約：KST Def3.1。使われ方：外積代数の基底変更射の生成元。 -/
def exteriorBaseChangeGenerator : S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) (ExteriorAlgebra.ι R)

/-- 概要：係数変更後の生成元の像は互いに反可換。
方針：両変数の tensor 帰納法で元の外積の反可換性へ帰着する。
規約：KST Def3.1、標数に制限なし。使われ方：和の平方零性。 -/
theorem exteriorBaseChangeGenerator_anticomm (x y : S ⊗[R] M) :
    exteriorBaseChangeGenerator x * exteriorBaseChangeGenerator y +
      exteriorBaseChangeGenerator y * exteriorBaseChangeGenerator x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | tmul t n =>
      change (s ⊗ₜ[R] ExteriorAlgebra.ι R m) * (t ⊗ₜ[R] ExteriorAlgebra.ι R n) +
        (t ⊗ₜ[R] ExteriorAlgebra.ι R n) * (s ⊗ₜ[R] ExteriorAlgebra.ι R m) = 0
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm t s, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap,
        TensorProduct.tmul_zero]
    | add y z hy hz =>
      simp only [map_add, mul_add, add_mul]
      calc
        _ = (exteriorBaseChangeGenerator (s ⊗ₜ[R] m) * exteriorBaseChangeGenerator y +
          exteriorBaseChangeGenerator y * exteriorBaseChangeGenerator (s ⊗ₜ[R] m)) +
          (exteriorBaseChangeGenerator (s ⊗ₜ[R] m) * exteriorBaseChangeGenerator z +
          exteriorBaseChangeGenerator z * exteriorBaseChangeGenerator (s ⊗ₜ[R] m)) := by abel
        _ = 0 := by rw [hy, hz, zero_add]
  | add x z hx hz =>
    simp only [map_add, add_mul, mul_add]
    calc
      _ = (exteriorBaseChangeGenerator x * exteriorBaseChangeGenerator y +
        exteriorBaseChangeGenerator y * exteriorBaseChangeGenerator x) +
        (exteriorBaseChangeGenerator z * exteriorBaseChangeGenerator y +
        exteriorBaseChangeGenerator y * exteriorBaseChangeGenerator z) := by abel
      _ = 0 := by rw [hx, hz, zero_add]

/-- 概要：係数変更後の生成元写像の値は平方零。
方針：純粋 tensor での平方零性と和の交差項の反可換性を使う。
規約：KST Def3.1、2で割らない。使われ方：ExteriorAlgebra.lift の関係式。 -/
theorem exteriorBaseChangeGenerator_sq_zero (x : S ⊗[R] M) :
    exteriorBaseChangeGenerator x * exteriorBaseChangeGenerator x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change (s ⊗ₜ[R] ExteriorAlgebra.ι R m) * (s ⊗ₜ[R] ExteriorAlgebra.ι R m) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero, TensorProduct.tmul_zero]
  | add x y hx hy =>
    simp only [map_add, add_mul, mul_add]
    rw [hx, hy, zero_add, add_zero]
    exact exteriorBaseChangeGenerator_anticomm y x

end SerrePositivity.KST.DerivedBlowup
