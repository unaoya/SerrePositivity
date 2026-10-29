module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-! # 核を消す Frobenius 冪の降下

概要：標数 `p` の環の全射 `f : A → B` の核の元を `x ↦ x^{p^n}` が消すなら、Frobenius 冪は `B → A` の環準同型へ降りる。
核が冪零なら、そのような `n` が取れる（`I^N = 0` なら `n = N`）。
方針：降下は Mathlib の `RingHom.liftOfSurjective`。`N < p^N` から `I^{p^N} = 0`。
規約：完全体・p 基底は仮定しない。
使われ方：p 基底の持ち上げ（`PBasisLifting`）と完全環からの写像の持ち上げ（`PerfectNilpotentLifting`）。
-/

@[expose] public section
namespace SerrePositivity

/-- `I^N = 0` なら、`I` の全ての元は `p^N` 乗で消える。 -/
theorem pow_exp_eq_zero_of_pow_eq_bot (p : ℕ) [hp : Fact p.Prime] {A : Type*} [CommRing A]
    (I : Ideal A) {N : ℕ} (hN : I ^ N = ⊥) : ∀ x ∈ I, x ^ p ^ N = 0 := by
  intro x hx
  have hn : N < p ^ N := Nat.lt_pow_self hp.out.one_lt
  have he : I ^ p ^ N = ⊥ := le_bot_iff.mp (by
    simpa only [hN] using (Ideal.pow_le_pow_right (I := I) hn.le))
  simpa only [he, Ideal.mem_bot] using Ideal.pow_mem_pow hx (p ^ N)

/-- 冪零イデアルの全ての元を、一つの p の冪指数で消せる。 -/
theorem exists_pow_exp_eq_zero_of_nilpotent_ideal
    (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A]
    (I : Ideal A) (hI : IsNilpotent I) : ∃ n : ℕ, ∀ x ∈ I, x ^ p ^ n = 0 := by
  obtain ⟨N, hN⟩ := hI
  exact ⟨N, pow_exp_eq_zero_of_pow_eq_bot p I (by simpa only [Ideal.zero_eq_bot] using hN)⟩

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
