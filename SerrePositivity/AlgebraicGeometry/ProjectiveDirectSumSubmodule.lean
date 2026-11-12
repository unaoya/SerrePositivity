module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
概要：成分ごとの部分加群の直和を、周囲の直和の部分加群と比較する。
方針：各成分の包含の直和の単射性と像の公式を使う。
規約：成分の添字に有限性を仮定しない。
使われ方：Rees 次数ごとの斉次局所化の直和を周囲の加群内で判定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum
variable {R κ : Type*} [CommRing R] [DecidableEq κ]
variable {M : κ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- 周囲の直和のうち、各成分が指定部分加群に入るもの。 -/
def projectiveDirectSumSubmodule (V : ∀ i, Submodule R (M i)) :
    Submodule R (⨁ i, M i) :=
  (Submodule.pi Set.univ V).comap (DirectSum.coeFnLinearMap R)

/-- 直和の部分加群への所属は成分ごとに判定する。 -/
@[simp]
theorem mem_projectiveDirectSumSubmodule (V : ∀ i, Submodule R (M i)) (x : ⨁ i, M i) :
    x ∈ projectiveDirectSumSubmodule V ↔ ∀ i, x i ∈ V i := by
  simp [projectiveDirectSumSubmodule, Submodule.mem_pi]

/-- 部分加群の包含の直和の像。 -/
theorem projectiveDirectSumSubmodule_range (V : ∀ i, Submodule R (M i)) :
    LinearMap.range (DirectSum.lmap (fun i ↦ (V i).subtype)) =
      projectiveDirectSumSubmodule V := by
  rw [DirectSum.range_lmap]
  simp only [Submodule.range_subtype, projectiveDirectSumSubmodule]

/-- 部分加群の直和と、周囲の直和の成分ごとの部分加群の同値。 -/
def projectiveDirectSumSubmoduleLinearEquiv (V : ∀ i, Submodule R (M i)) :
    (⨁ i, V i) ≃ₗ[R] projectiveDirectSumSubmodule V :=
  (LinearEquiv.ofInjective (DirectSum.lmap (fun i ↦ (V i).subtype))
    ((DirectSum.lmap_injective _).mpr (fun i ↦ Subtype.val_injective))).trans
      (LinearEquiv.ofEq _ _ (projectiveDirectSumSubmodule_range V))

/-- 部分加群の直和の比較は、周囲の直和への成分ごとの包含そのもの。 -/
@[simp]
theorem projectiveDirectSumSubmoduleLinearEquiv_val (V : ∀ i, Submodule R (M i))
    (x : ⨁ i, V i) :
    (projectiveDirectSumSubmoduleLinearEquiv V x).val =
      DirectSum.lmap (fun i ↦ (V i).subtype) x := rfl

end SerrePositivity.AlgebraicGeometry
