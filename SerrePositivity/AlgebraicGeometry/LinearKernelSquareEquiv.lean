module

public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
概要：可換な線形同型の正方形を、実際の核の線形同型へ制限する。
方針：順写像と逆写像を部分型上に明示する。
規約：核の同型の台は元の正方形の射そのもの。
使われ方：Čech 底変換の次数零の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M N : Type v} {P Q : Type w}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
variable (e : M ≃ₗ[R] P) (e' : N ≃ₗ[R] Q)
variable (h : ∀ x, g (e x) = e' (f x))

/-- 可換な正方形の同型を核に制限する。 -/
def linearKernelEquivOfCommute : LinearMap.ker f ≃ₗ[R] LinearMap.ker g where
  toFun x := ⟨e x, by change g (e x) = 0; rw [h, x.property, map_zero]⟩
  invFun y := ⟨e.symm y, by
    apply e'.injective
    rw [map_zero, ← h, e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' r x := Subtype.ext (e.map_smul r x)

/-- 核の比較の順写像は、元の線形同型そのもの。 -/
theorem linearKernelEquivOfCommute_apply (x : LinearMap.ker f) :
    (linearKernelEquivOfCommute f g e e' h x).val = e x := rfl

/-- 核の比較の逆写像は、元の線形同型の逆そのもの。 -/
theorem linearKernelEquivOfCommute_symm_apply (y : LinearMap.ker g) :
    ((linearKernelEquivOfCommute f g e e' h).symm y).val = e.symm y := rfl

end SerrePositivity.AlgebraicGeometry
