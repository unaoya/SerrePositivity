module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Module

/-!
概要：直和からの R 線形写像を、単項式と各成分での式から Rees 線形にする。
方針：Rees 元を係数の単項式の有限和に分け、直和の元について帰納する。
規約：成分自体に Rees 作用は要らず、直和全体と終域の作用だけを使う。
使われ方：Čech コホモロジーの直和から像の Rees 加群への全射を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum BigOperators

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {H : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable [Module (reesAlgebra I) (⨁ n, H n)] [Module (reesAlgebra I) N]
variable (f : (⨁ n, H n) →ₗ[R] N)
variable (hf : ∀ i j (a : R) (ha : a ∈ I ^ i) (x : H j),
  f ((⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
    DirectSum.lof R ℕ H j x) =
  (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
    f (DirectSum.lof R ℕ H j x))

include hf

/-- 単項式と各直和成分で作用と可換なら、すべての Rees 元の作用と可換。 -/
theorem reesDirectSumLinearMap_smul_of_monomial_lof (b : reesAlgebra I) (x : ⨁ n, H n) :
    f (b • x) = b • f x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | of j x =>
    change f (b • DirectSum.lof R ℕ H j x) = b • f (DirectSum.lof R ℕ H j x)
    rw [reesAlgebra.as_sum_support b]
    simp only [Finset.sum_smul, map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    exact hf i j (b.val.coeff i) (b.property i) x
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- 単項式と各成分での可換性から、同じ値の Rees 線形写像を作る。 -/
def reesDirectSumLinearMapOfMonomialLof : (⨁ n, H n) →ₗ[reesAlgebra I] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := reesDirectSumLinearMap_smul_of_monomial_lof I f hf

/-- Rees 線形にした写像の元への値は変わらない。 -/
@[simp] theorem reesDirectSumLinearMapOfMonomialLof_apply (x : ⨁ n, H n) :
    reesDirectSumLinearMapOfMonomialLof I f hf x = f x := rfl

/-- Rees 線形にする前の写像が全射なら、そのまま全射。 -/
theorem reesDirectSumLinearMapOfMonomialLof_surjective (h : Function.Surjective f) :
    Function.Surjective (reesDirectSumLinearMapOfMonomialLof I f hf) := h

end SerrePositivity.AlgebraicGeometry
