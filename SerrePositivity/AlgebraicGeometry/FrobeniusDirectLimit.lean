module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedFrobenius
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
概要：零環を許す p 乗写像の順極限と、有限段での零判定。
方針：p 乗環準同型の反復を有向系にし、代数的直極限の元の表示を使う。
規約：逆極限である Mathlib の Perfection は使わない。
使われ方：BST13 Lemma 3.5 の冪零不変性と普遍同相の計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hz : (p : A) = 0)

/-- 自然数段の間の、実際の Frobenius の反復。 -/
def frobeniusDirectSystemMap (i j : ℕ) (_h : i ≤ j) : A →+* A :=
  (projectivePrimePowerRingHom p hp hz) ^ (j - i)

/-- Frobenius の反復の有向系の法則。 -/
instance frobeniusDirectSystem : DirectedSystem (fun _ : ℕ ↦ A)
    (fun i j h ↦ frobeniusDirectSystemMap A p hp hz i j h) where
  map_self {i} x := by simp [frobeniusDirectSystemMap]
  map_map {k j i} hij hjk x := by
    simp only [frobeniusDirectSystemMap]
    change ((projectivePrimePowerRingHom p hp hz) ^ (_ - _) *
      (projectivePrimePowerRingHom p hp hz) ^ (_ - _)) x = _
    rw [← pow_add]
    congr 2
    omega

/-- Frobenius の反復の値は p の冪乗である。 -/
theorem frobeniusDirectSystemMap_apply (i j : ℕ) (h : i ≤ j) (x : A) :
    frobeniusDirectSystemMap A p hp hz i j h x = x ^ (p ^ (j - i)) := by
  have hi : ∀ n (a : A), (projectivePrimePowerRingHom p hp hz ^ n) a = a ^ (p ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ]
      change (projectivePrimePowerRingHom p hp hz ^ n) (a ^ p) = _
      rw [ih]
      simp only [← pow_mul, pow_succ, Nat.mul_comm]
  exact hi _ x

/-- Frobenius 順極限の環。零環でも同じ構成を使う。 -/
abbrev FrobeniusDirectLimit :=
  _root_.DirectLimit (fun _ : ℕ ↦ A) (frobeniusDirectSystemMap A p hp hz)

/-- 有限段から Frobenius 順極限への環準同型。 -/
def frobeniusDirectLimitOf (n : ℕ) : A →+* FrobeniusDirectLimit A p hp hz :=
  DirectLimit.Ring.of (fun _ : ℕ ↦ A) (frobeniusDirectSystemMap A p hp hz) n

/-- 有限段の元が零になるのは、ある先の p 乗反復で零になる場合に限る。 -/
theorem frobeniusDirectLimitOf_eq_zero_iff (n : ℕ) (x : A) :
    frobeniusDirectLimitOf A p hp hz n x = 0 ↔
      ∃ m, ∃ h : n ≤ m, frobeniusDirectSystemMap A p hp hz n m h x = 0 := by
  change (⟦⟨n, x⟩⟧ : FrobeniusDirectLimit A p hp hz) = 0 ↔ _
  exact _root_.DirectLimit.exists_eq_zero (G := fun _ : ℕ ↦ A)
    (f := frobeniusDirectSystemMap A p hp hz) ⟨n, x⟩

/-- 有限段の二つの元の像は、Frobenius を十分反復して一致する場合に限り等しい。 -/
theorem frobeniusDirectLimitOf_eq_iff (n m : ℕ) (x y : A) :
    frobeniusDirectLimitOf A p hp hz n x = frobeniusDirectLimitOf A p hp hz m y ↔
      ∃ k, ∃ hn : n ≤ k, ∃ hm : m ≤ k,
        frobeniusDirectSystemMap A p hp hz n k hn x =
          frobeniusDirectSystemMap A p hp hz m k hm y := by
  change (⟦⟨n, x⟩⟧ : FrobeniusDirectLimit A p hp hz) = ⟦⟨m, y⟩⟧ ↔ _
  exact Quotient.eq

/-- 有限段の元は、その元が冪零である場合に限って Frobenius 順極限で零になる。 -/
theorem frobeniusDirectLimitOf_eq_zero_iff_nilpotent (n : ℕ) (x : A) :
    frobeniusDirectLimitOf A p hp hz n x = 0 ↔ IsNilpotent x := by
  rw [frobeniusDirectLimitOf_eq_zero_iff]
  constructor
  · rintro ⟨m, h, hx⟩
    exact ⟨p ^ (m - n), (frobeniusDirectSystemMap_apply A p hp hz n m h x).symm.trans hx⟩
  · rintro ⟨k, hk⟩
    refine ⟨n + k, Nat.le_add_right n k, ?_⟩
    rw [frobeniusDirectSystemMap_apply, Nat.add_sub_cancel_left]
    exact pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)) hk

end SerrePositivity.AlgebraicGeometry
