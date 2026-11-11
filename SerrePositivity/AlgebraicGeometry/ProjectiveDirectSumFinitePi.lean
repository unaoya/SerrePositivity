module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi

/-!
概要：任意直和と有限個の係数の積の交換を線形同値として与える。
方針：各座標への写像を直和に送り、逆を有限個の座標包含の和で作る。
規約：有限性を要求するのは積の添字だけ。
使われ方：Rees 次数の直和を、有限な標準開 Čech の各項と交換する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum

variable {R κ τ : Type*} [CommRing R] [DecidableEq κ] [DecidableEq τ] [Fintype τ]
variable (M : κ → τ → Type*) [∀ i j, AddCommGroup (M i j)] [∀ i j, Module R (M i j)]

/-- 直和の各元の座標を、座標ごとの直和へ送る。 -/
def projectiveDirectSumToFinitePi :
    (⨁ i, ∀ j, M i j) →ₗ[R] ∀ j, ⨁ i, M i j :=
  LinearMap.pi (fun j ↦ DirectSum.lmap (fun i ↦ LinearMap.proj j))

/-- 各座標の直和を、有限個の座標包含の和でまとめる。 -/
def projectiveFinitePiToDirectSum :
    (∀ j, ⨁ i, M i j) →ₗ[R] ⨁ i, ∀ j, M i j :=
  ∑ j, (DirectSum.lmap (fun i ↦ LinearMap.single R (M i) j)).comp (LinearMap.proj j)

/-- 直和と有限積の交換。 -/
def projectiveDirectSumFinitePiLinearEquiv :
    (⨁ i, ∀ j, M i j) ≃ₗ[R] ∀ j, ⨁ i, M i j := by
  refine LinearEquiv.ofLinearMap (projectiveDirectSumToFinitePi M)
    (projectiveFinitePiToDirectSum M) ?_ ?_
  · apply LinearMap.ext
    intro x
    funext j
    apply DFinsupp.ext
    intro i
    simp [projectiveDirectSumToFinitePi, projectiveFinitePiToDirectSum,
      DirectSum.sum_apply, LinearMap.sum_apply]
  · apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    funext j
    simp [projectiveDirectSumToFinitePi, projectiveFinitePiToDirectSum,
      DirectSum.sum_apply, LinearMap.sum_apply]

/-- 同値は、Rees 次数と Čech 項の座標を交換する。 -/
@[simp]
theorem projectiveDirectSumFinitePiLinearEquiv_apply
    (x : ⨁ i, ∀ j, M i j) (j : τ) (i : κ) :
    projectiveDirectSumFinitePiLinearEquiv (R := R) M x j i = x i j := rfl

/-- 有限積との比較は、各成分の係数写像に自然。 -/
theorem projectiveDirectSumFinitePiLinearEquiv_naturality
    (N : κ → τ → Type*) [∀ i j, AddCommGroup (N i j)] [∀ i j, Module R (N i j)]
    (f : ∀ i j, M i j →ₗ[R] N i j) (x : ⨁ i, ∀ j, M i j) :
    projectiveDirectSumFinitePiLinearEquiv (R := R) N
      (DirectSum.lmap (fun i ↦ LinearMap.pi (fun j ↦ (f i j).comp (LinearMap.proj j))) x) =
        fun j ↦ DirectSum.lmap (fun i ↦ f i j) (projectiveDirectSumFinitePiLinearEquiv (R := R) M x j) := by
  funext j
  apply DFinsupp.ext
  intro i
  rfl

end SerrePositivity.AlgebraicGeometry
