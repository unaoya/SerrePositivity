module

public import SerrePositivity.BhattScholze.DeltaWittGhostStep
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.WittVector.Basic

/-! # δFrobeniusをghost座標に持つ全Witt係数の構成

有限prefixの延長で既定係数を保存し、整合した対角列を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 既定係数を保存してghost等式を一段ずつ延長する有限prefix。 -/
def deltaWittGhostPrefix (D : DeltaStructure p A) (a : A) : ℕ → (ℕ → A)
  | 0 => fun _ => a
  | n + 1 => Function.update (deltaWittGhostPrefix D a n) (n + 1)
      (Classical.epsilon fun c => D.frobeniusLift^[n + 1] a =
        (∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
          (deltaWittGhostPrefix D a n i) ^ (p ^ (n + 1 - i))) +
          (p : A) ^ (n + 1) * c)

private theorem deltaWittGhostPrefix_succ_of_le (D : DeltaStructure p A) (a : A)
    (n i : ℕ) (hi : i ≤ n) : deltaWittGhostPrefix D a (n + 1) i = deltaWittGhostPrefix D a n i := by
  simp only [deltaWittGhostPrefix, Function.update_of_ne (by omega : i ≠ n + 1)]

private theorem deltaWittGhostPrefix_ghost (D : DeltaStructure p A) (a : A) (n : ℕ) :
    ∀ m ≤ n, D.frobeniusLift^[m] a =
      ∑ i ∈ Finset.range (m + 1), (p : A) ^ i * (deltaWittGhostPrefix D a n i) ^ (p ^ (m - i)) := by
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst m
      simp [deltaWittGhostPrefix]
  | succ n ih =>
      intro m hm
      by_cases hmn : m ≤ n
      · rw [ih m hmn]
        apply Finset.sum_congr rfl
        intro i hi
        rw [deltaWittGhostPrefix_succ_of_le D a n i (by have := Finset.mem_range.mp hi; omega)]
      · have hm' : m = n + 1 := by omega
        subst m
        have hc := Classical.epsilon_spec
          (D.exists_next_ghost_coefficient a (deltaWittGhostPrefix D a n) n (ih n le_rfl))
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, pow_zero, pow_one]
        have hs : (∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
            (deltaWittGhostPrefix D a (n + 1) i) ^ (p ^ (n + 1 - i))) =
            ∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
              (deltaWittGhostPrefix D a n i) ^ (p ^ (n + 1 - i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [deltaWittGhostPrefix_succ_of_le D a n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
        rw [hs]
        simpa only [deltaWittGhostPrefix, Function.update_self] using hc

private theorem deltaWittGhostPrefix_agrees (D : DeltaStructure p A) (a : A)
    (n i : ℕ) (hi : i ≤ n) :
    deltaWittGhostPrefix D a n i = deltaWittGhostPrefix D a i i := by
  induction n with
  | zero => have := Nat.eq_zero_of_le_zero hi; subst i; rfl
  | succ n ih =>
      by_cases hin : i ≤ n
      · rw [deltaWittGhostPrefix_succ_of_le D a n i hin, ih hin]
      · have h : i = n + 1 := by omega
        subst i
        rfl

/-- δFrobeniusの全反復をghost等式で実現する、具体的なWitt係数列。 -/
def deltaWittGhostCoefficients (D : DeltaStructure p A) (a : A) : ℕ → A :=
  fun n => deltaWittGhostPrefix D a n n

/-- 構成した全係数列のghost等式。p正則性や完備性は存在には不要。 -/
theorem deltaWittGhostCoefficients_ghost (D : DeltaStructure p A) (a : A) (n : ℕ) :
    D.frobeniusLift^[n] a =
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
        deltaWittGhostCoefficients D a i ^ (p ^ (n - i)) := by
  rw [deltaWittGhostPrefix_ghost D a n n le_rfl]
  apply Finset.sum_congr rfl
  intro i hi
  rw [deltaWittGhostPrefix_agrees D a n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  rfl

/-- δFrobeniusを全ghost座標に持つ点ごとのWitt元。環射性は別工程。 -/
def deltaWittGhostVector (D : DeltaStructure p A) (a : A) : WittVector p A :=
  WittVector.mk p (deltaWittGhostCoefficients D a)

/-- 構成したWitt元の全ghost座標は基底Frobeniusの反復。 -/
theorem deltaWittGhostVector_ghostComponent (D : DeltaStructure p A) (a : A) (n : ℕ) :
    WittVector.ghostComponent n (deltaWittGhostVector D a) = D.frobeniusLift^[n] a := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.aeval_X,
    map_natCast, deltaWittGhostVector, WittVector.coeff_mk]
  exact (deltaWittGhostCoefficients_ghost D a n).symm

/-- 構成した点ごとのWitt元は第0係数射の断面になる。 -/
@[simp] theorem deltaWittGhostVector_coeff_zero (D : DeltaStructure p A) (a : A) :
    (deltaWittGhostVector D a).coeff 0 = a := rfl

end SerrePositivity.BhattScholze
