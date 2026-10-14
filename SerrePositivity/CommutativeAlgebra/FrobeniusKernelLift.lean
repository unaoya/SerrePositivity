module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Maps

/-! # 核を消す Frobenius 冪の降下

完全体・p-basis を仮定せず、一つの Frobenius 冪を全射の終域へ降下する。
-/

@[expose] public section
namespace SerrePositivity

variable {A B : Type*} [CommRing A] [CommRing B]
variable (p : ℕ) [Fact p.Prime] [CharP A p]

/-- 核を消す Frobenius 冪を全射の終域から元の環への写像として降ろす。 -/
noncomputable def liftFrobeniusOfSurjective (f : A →+* B) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) : B →+* A :=
  f.liftOfSurjective hf ⟨iterateFrobenius A p n, fun x hx ↦ hkill x hx⟩

@[simp] theorem liftFrobeniusOfSurjective_apply_map (f : A →+* B) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) (x : A) :
    liftFrobeniusOfSurjective p f hf n hkill (f x) = x ^ p ^ n :=
  RingHom.liftOfSurjective_comp_apply f hf _ x

theorem map_liftFrobeniusOfSurjective (f : A →+* B) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) (x : B) :
    f (liftFrobeniusOfSurjective p f hf n hkill x) = x ^ p ^ n := by
  obtain ⟨y, rfl⟩ := hf x
  rw [liftFrobeniusOfSurjective_apply_map, map_pow]

end SerrePositivity
