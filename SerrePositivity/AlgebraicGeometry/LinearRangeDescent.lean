module

public import Mathlib.LinearAlgebra.Isomorphisms

/-!
概要：核の包含を使い、線形写像を別の写像の像から降ろす。
方針：核による商と像の標準同型を使う。
規約：像の元の代表を新しく選ばず、標準的な線形写像として降ろす。
使われ方：閉厚化への射影の像を、I 進剰余類へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R M N P : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- ker f⊆ker g なら、g を f の像から降ろせる。 -/
def linearRangeDescent (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : LinearMap.range f →ₗ[R] P :=
  ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap

/-- 像から降ろした写像を元の代表で計算する。 -/
@[simp] theorem linearRangeDescent_rangeRestrict (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (x : M) :
    linearRangeDescent f g h (f.rangeRestrict x) = g x := by
  change (LinearMap.ker f).liftQ g h (f.quotKerEquivRange.symm (f.rangeRestrict x)) = g x
  have he : f.rangeRestrict x = f.quotKerEquivRange ((LinearMap.ker f).mkQ x) :=
    Subtype.ext rfl
  rw [he, LinearEquiv.symm_apply_apply]
  rfl

end SerrePositivity.AlgebraicGeometry
