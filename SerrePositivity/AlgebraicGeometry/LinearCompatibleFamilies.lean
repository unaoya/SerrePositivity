module

public import Mathlib.LinearAlgebra.Pi

/-!
概要：線形な遷移写像に関する互換族を、積加群の部分加群として扱う。
方針：互換性を成分ごとの等式で定義する。
規約：ここで互換族を定義するだけなら、遷移の恒等・合成則は要らない。
使われ方：閉厚化の Čech コホモロジーの互換族と I 進完備化の比較。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type*} [Semiring R] {Q : ℕ → Type*}
variable [∀ n, AddCommMonoid (Q n)] [∀ n, Module R (Q n)]

/-- 線形な遷移写像に関する互換族の部分加群。 -/
def compatibleLinearFamilies (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j) :
    Submodule R (∀ n, Q n) where
  carrier := {x | ∀ i j (h : j ≤ i), t i j h (x i) = x j}
  zero_mem' := by intro i j h; exact map_zero (t i j h)
  add_mem' := by
    intro x y hx hy i j h
    exact (t i j h).map_add (x i) (y i) |>.trans (congrArg₂ (· + ·) (hx i j h) (hy i j h))
  smul_mem' := by
    intro a x hx i j h
    exact ((t i j h).map_smul a (x i)).trans (congrArg (a • ·) (hx i j h))

/-- 互換族を第 n 成分で評価する線形写像。 -/
def compatibleLinearFamiliesEval (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j) (n : ℕ) :
    compatibleLinearFamilies t →ₗ[R] Q n :=
  (LinearMap.proj n).comp (compatibleLinearFamilies t).subtype

end SerrePositivity.AlgebraicGeometry
