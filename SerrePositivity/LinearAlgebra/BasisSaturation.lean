module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-! # 基底の部分集合の線形包の飽和性

基底の任意の部分集合 `s` が張る部分加群は、左非零因子による除算について飽和している：
`a` が左非零因子（`a * y = 0 → y = 0`）で `a • x` がその部分加群に属すれば、`x` も属す。
Mathlib の `Module.Basis.mem_span_image`（所属を座標の台で判定する）に帰着する。
係数環は非可換の半環でよい。`s` が全体でなければ、`a` が左非零因子であることは必要でもある。
-/

@[expose] public section
namespace SerrePositivity

open Submodule

/-- 基底の部分集合の線形包は、左非零因子による除算について飽和。 -/
theorem basis_mem_span_image_of_smul_mem
    {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (B : Module.Basis ι R M) (s : Set ι) {a : R} (ha : a ∈ nonZeroDivisorsLeft R) {x : M}
    (hx : a • x ∈ span R (B '' s)) : x ∈ span R (B '' s) := by
  rw [B.mem_span_image] at hx ⊢
  intro j hj
  apply hx
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, map_smul, Finsupp.smul_apply,
    smul_eq_mul] at hj ⊢
  exact fun h ↦ hj (ha _ h)

end SerrePositivity
