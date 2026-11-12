module

public import Mathlib.LinearAlgebra.Isomorphisms

/-!
概要：同じ核を持つ二つの全射から、商の canonical な比較を作る。
方針：元の加群の核による商を共通に通す。
規約：比較は元の加群からの射影と可換であることまで示す。
使われ方：Rees の商の Čech 係数と実際の閉厚化の切断の自然な同定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M N P : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]
variable (f : M →ₗ[R] N) (g : M →ₗ[R] P)
variable (hf : Function.Surjective f) (hg : Function.Surjective g)
variable (hker : LinearMap.ker f = LinearMap.ker g)

/-- 同じ核を持つ二つの全射の、共通の元の加群から定まる比較。 -/
def cechQuotientComparison : N ≃ₗ[R] P :=
  (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (g.quotKerEquivOfSurjective hg))

/-- 商の比較は、元の加群からの二つの射影と可換。 -/
theorem cechQuotientComparison_projection (x : M) :
    cechQuotientComparison f g hf hg hker (f x) = g x := by
  have h : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x :=
    (f.quotKerEquivOfSurjective hf).symm_apply_eq.mpr rfl
  dsimp only [cechQuotientComparison, LinearEquiv.trans_apply]
  rw [h]
  rfl

end SerrePositivity.AlgebraicGeometry
