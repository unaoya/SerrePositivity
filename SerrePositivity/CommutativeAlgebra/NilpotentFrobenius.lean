module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-! # 冪零イデアルを消す一つの p 冪

完全体・任意の p-basis の持ち上げで使う共通の冪指数評価。
この評価自体には環の標数の仮定は不要。
-/

public section
namespace SerrePositivity

/-- 冪零イデアルの全ての元を、一つの p の冪指数で消せる。 -/
theorem exists_pow_exp_eq_zero_of_nilpotent_ideal
    (p : ℕ) [hp : Fact p.Prime] {A : Type*} [CommRing A]
    (I : Ideal A) (hI : IsNilpotent I) : ∃ n : ℕ, ∀ x ∈ I, x ^ p ^ n = 0 := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, fun x hx ↦ ?_⟩
  have hn : N < p ^ N := Nat.lt_pow_self hp.out.one_lt
  have he : I ^ p ^ N = ⊥ := le_bot_iff.mp (by
    simpa only [hN, Ideal.zero_eq_bot] using (Ideal.pow_le_pow_right (I := I) hn.le))
  simpa only [he, Ideal.mem_bot] using Ideal.pow_mem_pow hx (p ^ N)

end SerrePositivity
