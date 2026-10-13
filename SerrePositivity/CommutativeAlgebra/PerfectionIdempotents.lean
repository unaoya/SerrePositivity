module

public import Mathlib.RingTheory.Perfection
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Tactic.Ring

/-! # Perfection の係数による冪等元の検出

第零係数は一般には単射でないが、冪等元が零であることを検出する。
Witt係数の積の方程式から単元性を得るための一般環論も分離する。
perfectoid性や被約性の引用は用いない。
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- Perfection の冪等元は、第零係数が零なら零。 -/
theorem perfection_idempotent_eq_zero_of_coeff_zero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (e : Perfection R p) (he : IsIdempotentElem e)
    (hzero : Perfection.coeff R p 0 e = 0) : e = 0 := by
  apply Perfection.ext
  intro n
  have hn : IsIdempotentElem (Perfection.coeff R p n e) := by
    change Perfection.coeff R p n e * Perfection.coeff R p n e = Perfection.coeff R p n e
    rw [← map_mul, he.eq]
  have hp := Perfection.coeffMonoidHom_pow_p_pow_self e n
  change (Perfection.coeff R p n e) ^ (p ^ n) = Perfection.coeff R p 0 e at hp
  rw [hn.pow_eq (pow_ne_zero n (Fact.out : p.Prime).ne_zero), hzero] at hp
  simpa only [map_zero] using hp

/-- Perfection の第零係数が単元なら、各係数の逆元から元全体の逆元を構成できる。 -/
theorem perfection_isUnit_of_coeff_zero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a : Perfection R p) (ha : IsUnit (Perfection.coeff R p 0 a)) : IsUnit a := by
  have hunit (n : ℕ) : IsUnit (Perfection.coeff R p n a) := by
    apply (isUnit_pow_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
    rw [show (Perfection.coeff R p n a) ^ (p ^ n) = Perfection.coeff R p 0 a from
      Perfection.coeffMonoidHom_pow_p_pow_self a n]
    exact ha
  let b : Perfection R p := ⟨fun n ↦ Ring.inverse (Perfection.coeff R p n a), by
    intro n
    rw [Ring.inverse_pow, show (Perfection.coeff R p (n + 1) a) ^ p =
      Perfection.coeff R p n a from Perfection.coeffMonoidHom_pow_p' a n]⟩
  apply IsUnit.of_mul_eq_one b
  apply Perfection.ext
  intro n
  change Perfection.coeff R p n a * Ring.inverse (Perfection.coeff R p n a) = 1
  exact Ring.mul_inverse_cancel _ (hunit n)

/-- 第零・第一係数の積方程式と冪等元の検出から、因子の単元性を得る。
Wittベクトル自体の計算とは独立の可換環の補題。 -/
theorem isUnit_of_coefficient_equations
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hdetect : ∀ e : R, IsIdempotentElem e → f e = 0 → e = 0)
    (x a b y : R) (N : ℕ) (hN : 0 < N) (hxa : x * a = 0)
    (hfirst : x ^ N * b + y * a ^ N = 1) (hfx : f x = 0) : IsUnit a := by
  let e := x ^ N * b
  have hprod : e * (y * a ^ N) = 0 := by
    calc
      _ = (x * a) ^ N * (b * y) := by dsimp only [e]; ring
      _ = 0 := by rw [hxa, zero_pow (Nat.ne_of_gt hN), zero_mul]
  have hidem : IsIdempotentElem e := by
    have heq := congrArg (fun z : R ↦ e * z) hfirst
    change e * (e + y * a ^ N) = e * 1 at heq
    rw [mul_add, hprod, add_zero, mul_one] at heq
    exact heq
  have hfe : f e = 0 := by
    simp only [e, map_mul, map_pow, hfx, zero_pow (Nat.ne_of_gt hN), zero_mul]
  have hezero := hdetect e hidem hfe
  have hone : y * a ^ N = 1 := by
    change e + y * a ^ N = 1 at hfirst
    simpa only [hezero, zero_add] using hfirst
  exact (isUnit_pow_iff (Nat.ne_of_gt hN)).mp (IsUnit.of_mul_eq_one_right y hone)

end SerrePositivity
