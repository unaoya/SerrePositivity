module

public import SerrePositivity.AlgebraicGeometry.AwayPowerMap
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
概要：分母を冪に送る局所化の写像の半線形性。
方針：係数上の可換性を局所化へ移し、乗法でスカラー作用を照合する。
規約：係数の自己準同型を明示し、線形とは仮定しない。
使われ方：閉厚化の Frobenius を指定次数の加群へ制限する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (ρ : R →+* R) (f : A →+* B) (a : A) (b : B) (k : ℕ) (h : f a = b ^ k)
variable (hs : ∀ r, f (algebraMap R A r) = algebraMap R B (ρ r))

include hs in
/-- 局所化の延長も係数の自己準同型と可換。 -/
theorem awayPowerMap_scalar (r : R) :
    awayPowerMap f a b k h (algebraMap R (Localization.Away a) r) =
      algebraMap R (Localization.Away b) (ρ r) := by
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away a), awayPowerMap_algebraMap,
    hs, ← IsScalarTower.algebraMap_apply R B (Localization.Away b)]

/-- 局所化の環準同型を、係数自己準同型に関する半線形写像として扱う。 -/
def awayPowerMapSemilinear : Localization.Away a →ₛₗ[ρ] Localization.Away b where
  toFun := awayPowerMap f a b k h
  map_add' := (awayPowerMap f a b k h).map_add
  map_smul' r x := by
    rw [Algebra.smul_def, map_mul, awayPowerMap_scalar ρ f a b k h hs, Algebra.smul_def]

/-- 半線形写像と元の局所化の環準同型の値は一致する。 -/
theorem awayPowerMapSemilinear_apply (x : Localization.Away a) :
    awayPowerMapSemilinear ρ f a b k h hs x = awayPowerMap f a b k h x := rfl

end SerrePositivity.AlgebraicGeometry
