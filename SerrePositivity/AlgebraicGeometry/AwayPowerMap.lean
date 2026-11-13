module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：分母を冪に送る環準同型を、Away 局所化の間へ延長する。
方針：像の分母の可逆性で lift し、分数の式を可逆な分母との積で確かめる。
規約：指数は零も許し、環の非自明性は仮定しない。
使われ方：閉厚化の反復 Frobenius を標準開へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable (f : A →+* B) (a : A) (b : B) (k : ℕ) (h : f a = b ^ k)

/-- 分母の像が b の冪であるとき、実際の Away 局所化の間に誘導される環準同型。 -/
def awayPowerMap : Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (g := (algebraMap B (Localization.Away b)).comp f) (by
    change IsUnit (algebraMap B (Localization.Away b) (f a))
    rw [h, map_pow]
    exact IsLocalization.Away.algebraMap_pow_isUnit b k)

/-- 局所化の延長は、元の環の写像を保つ。 -/
theorem awayPowerMap_algebraMap (x : A) :
    awayPowerMap f a b k h (algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away b) (f x) :=
  IsLocalization.Away.lift_eq _ _ _

/-- 分母 a^n の分数は、分母 b^(k*n) の分数へ送られる。 -/
theorem awayPowerMap_fraction (x : A) (n : ℕ) :
    awayPowerMap f a b k h
      (IsLocalization.mk' (Localization.Away a) x (⟨a ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers a)) =
    IsLocalization.mk' (Localization.Away b) (f x) (⟨b ^ (k * n), ⟨k * n, rfl⟩⟩ : Submonoid.powers b) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  have hd : algebraMap B (Localization.Away b) (b ^ (k * n)) =
      awayPowerMap f a b k h (algebraMap A (Localization.Away a) (a ^ n)) := by
    simp only [awayPowerMap_algebraMap, map_pow, h, pow_mul]
  change awayPowerMap f a b k h _ * algebraMap B (Localization.Away b) (b ^ (k * n)) = _
  rw [hd, ← map_mul, IsLocalization.mk'_spec, awayPowerMap_algebraMap]

end SerrePositivity.AlgebraicGeometry
