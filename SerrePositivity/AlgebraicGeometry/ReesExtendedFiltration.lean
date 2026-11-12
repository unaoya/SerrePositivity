module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module

/-!
概要：基底のイデアルの冪で定まるフィルトレーションを、係数環の制限で比較する。
方針：イデアルの像と冪の交換、既存の restrictScalars_map_smul_eq を使う。
規約：写像と次数分解は基底環上で線形であればよい。
使われ方：Rees 加群の Proj 次数への射影が、各 IⁿM を保つことの証明。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (I : Ideal R)

/-- 拡大イデアルの冪の作用を制限すると、基底のイデアルの冪の作用になる。 -/
theorem reesExtendedAdic_restrictScalars (n : ℕ) :
    ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)).restrictScalars R =
      I ^ n • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- 基底環上の線形写像は、拡大イデアルによる I 進フィルトレーションを保つ。 -/
theorem reesExtendedAdic_map_mem (f : M →ₗ[R] N) (n : ℕ) (x : M)
    (hx : x ∈ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)) :
    f x ∈ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N) := by
  change x ∈ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)).restrictScalars R at hx
  rw [reesExtendedAdic_restrictScalars] at hx
  change f x ∈ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N)).restrictScalars R
  rw [reesExtendedAdic_restrictScalars]
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) f hx

/-- Proj 次数の斉次成分への射影は、各 IⁿM を保つ。 -/
theorem reesExtendedAdic_decompose_mem {κ : Type*} [DecidableEq κ]
    (G : κ → Submodule R M) [DirectSum.Decomposition G]
    (d : κ) (n : ℕ) (x : M)
    (hx : x ∈ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)) :
    (DirectSum.decompose G x d : M) ∈
      (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M) :=
  reesExtendedAdic_map_mem (S := S) I
    ((G d).subtype.comp ((DirectSum.component R κ (fun d ↦ G d) d).comp
      (DirectSum.decomposeLinearEquiv G).toLinearMap)) n x hx

end SerrePositivity.AlgebraicGeometry
