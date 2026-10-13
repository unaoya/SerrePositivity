module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maps

/-! # 互換的な根が生成する反復 Frobenius の核

標数 p の環で Frobenius が全射なら、最初の核の一つの生成元の互換的な根から、
各反復の核の生成元を得る。係数の根を選び、対応する積を引くことにより、
一つ前の核へ帰着する。Noether 性・被約性・perfectoid 性は仮定しない。
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- 互換的な p 乗根の列の、任意の二段の間の冪関係。 -/
theorem compatibleRoots_pow
    {R : Type u} [Monoid R] (p : ℕ) (e : ℕ → R)
    (he : ∀ n, e (n + 1) ^ p = e n) (m n : ℕ) :
    e (m + n) ^ (p ^ n) = e m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, ← Nat.add_assoc, he, ih]

/-- 互換的な根の生成する主イデアルは段を進めると大きくなる。 -/
theorem span_compatibleRoot_le_succ
    {R : Type u} [CommSemiring R] (p : ℕ) (hp : p ≠ 0) (e : ℕ → R)
    (he : ∀ n, e (n + 1) ^ p = e n) (n : ℕ) :
    Ideal.span {e n} ≤ Ideal.span {e (n + 1)} := by
  rw [Ideal.span_singleton_le_span_singleton, ← he n]
  exact dvd_pow_self _ hp

/-- Frobenius の全射性は、その任意の反復にも移る。 -/
theorem surjective_pow_prime_pow
    (R : Type u) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : Function.Surjective (frobenius R p)) (n : ℕ) :
    Function.Surjective (fun x : R => x ^ (p ^ n)) := by
  intro a
  obtain ⟨b, hb⟩ := hF.iterate n a
  exact ⟨b, by simpa only [iterate_frobenius] using hb⟩

/-- 最初の核と互換的な根の列から、反復 Frobenius の核を計算する。 -/
theorem frobenius_pow_kernel_iff_mem_span
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : Function.Surjective (frobenius R p)) (e : ℕ → R)
    (he0 : e 0 = 0) (he : ∀ n, e (n + 1) ^ p = e n)
    (hker : ∀ x : R, x ^ p = 0 ↔ x ∈ Ideal.span {e 1})
    (n : ℕ) (x : R) : x ^ (p ^ n) = 0 ↔ x ∈ Ideal.span {e n} := by
  induction n generalizing x with
  | zero => simp [he0]
  | succ n ih =>
    constructor
    · intro hx
      have hxp : (x ^ (p ^ n)) ^ p = 0 := by
        rw [← pow_mul, ← pow_succ]
        exact hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp ((hker _).mp hxp)
      obtain ⟨b, hb⟩ := surjective_pow_prime_pow R p hF n a
      change b ^ (p ^ n) = a at hb
      have hdiff : (x - e (n + 1) * b) ^ (p ^ n) = 0 := by
        rw [sub_pow_char_pow, mul_pow]
        have hroot : e (n + 1) ^ (p ^ n) = e 1 := by
          simpa only [Nat.add_comm] using compatibleRoots_pow p e he 1 n
        rw [hroot, hb, ← ha, sub_self]
      have hmem : x - e (n + 1) * b ∈ Ideal.span {e (n + 1)} :=
        span_compatibleRoot_le_succ p (Fact.out : p.Prime).ne_zero e he n
          ((ih _).mp hdiff)
      have hprod : e (n + 1) * b ∈ Ideal.span {e (n + 1)} :=
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      simpa only [sub_add_cancel] using (Ideal.span {e (n + 1)}).add_mem hmem hprod
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
      have hen : e (n + 1) ^ (p ^ (n + 1)) = 0 := by
        simpa only [Nat.zero_add, he0] using compatibleRoots_pow p e he 0 (n + 1)
      rw [mul_pow, hen, zero_mul]

/-- 理想としての反復 Frobenius の核の計算。 -/
theorem ker_iterateFrobenius_eq_span
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : Function.Surjective (frobenius R p)) (e : ℕ → R)
    (he0 : e 0 = 0) (he : ∀ n, e (n + 1) ^ p = e n)
    (hker : ∀ x : R, x ^ p = 0 ↔ x ∈ Ideal.span {e 1}) (n : ℕ) :
    RingHom.ker (iterateFrobenius R p n) = Ideal.span {e n} := by
  ext x
  rw [RingHom.mem_ker, iterateFrobenius_def]
  exact frobenius_pow_kernel_iff_mem_span R p hF e he0 he hker n x

end SerrePositivity
