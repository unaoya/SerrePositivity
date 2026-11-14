module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import Mathlib.RingTheory.WittVector.InitTail

/-!
# Witt 基底の p 進完備性

## 概要
p 正則な p 進完備環の Witt 環は p 進完備である。

## 方針
列の差分方程式を係数環で解く。第 0 成分の解を Teichmüller で持ち上げ、
誤差を Verschiebung で割って反復する。一意性は ghost 成分で示す。

## 規約
p 進完備性は主イデアル (p) に関する古典的完備性。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 基底と、大きい分冪模型の係数。
-/

public noncomputable section

open WittVector

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable [IsAdicComplete (Ideal.span {(p : C)}) C]

local notation "W" => WittVector p C

private def recurrenceHead (a : ℕ → W) : ℕ → C :=
  (adicRecurrenceMap_bijective (M := C) (p : C)).surjective
    (fun i => (a i).coeff 0) |>.choose

omit [Fact p.Prime] in
private theorem recurrenceHead_spec (a : ℕ → W) (i : ℕ) :
    recurrenceHead p C a i - (p : C) * recurrenceHead p C a (i + 1) = (a i).coeff 0 :=
  congrFun ((adicRecurrenceMap_bijective (M := C) (p : C)).surjective
    (fun i => (a i).coeff 0)).choose_spec i

private def recurrenceTail (a : ℕ → W) (i : ℕ) : W :=
  WittVector.mk p (fun j =>
    (a i - teichmuller p (recurrenceHead p C a i) +
      (p : W) * teichmuller p (recurrenceHead p C a (i + 1))).coeff (j + 1))

private theorem recurrenceTail_spec (a : ℕ → W) (i : ℕ) :
    verschiebung (recurrenceTail p C a i) =
      a i - teichmuller p (recurrenceHead p C a i) +
        (p : W) * teichmuller p (recurrenceHead p C a (i + 1)) := by
  ext j
  cases j with
  | zero =>
    rw [verschiebung_coeff_zero]
    change 0 = wZero p C (a i - teichmuller p (recurrenceHead p C a i) +
      (p : W) * teichmuller p (recurrenceHead p C a (i + 1)))
    simp only [map_add, map_sub, map_mul, map_natCast, wZero, constantCoeff_apply,
      teichmuller_coeff_zero]
    linear_combination (recurrenceHead_spec p C a i)
  | succ j => rfl

private def recurrenceLift (a : ℕ → W) (i : ℕ) : W :=
  WittVector.mk p (fun j => recurrenceHead p C ((recurrenceTail p C)^[j] a) i)

private theorem recurrenceLift_split (a : ℕ → W) (i : ℕ) :
    recurrenceLift p C a i = teichmuller p (recurrenceHead p C a i) +
      verschiebung (recurrenceLift p C (recurrenceTail p C a) i) := by
  ext j
  rw [WittVector.coeff_add_of_disjoint j _ _ (fun k => by
    cases k with
    | zero => exact Or.inr (verschiebung_coeff_zero _)
    | succ k => exact Or.inl (teichmuller_coeff_pos p _ (k + 1) (Nat.succ_pos k)))]
  cases j with
  | zero => rw [teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]; rfl
  | succ j =>
    rw [teichmuller_coeff_pos p _ (j + 1) (Nat.succ_pos j), verschiebung_coeff_succ, zero_add]
    change recurrenceHead p C ((recurrenceTail p C)^[j + 1] a) i =
      recurrenceHead p C ((recurrenceTail p C)^[j] (recurrenceTail p C a)) i
    rw [Function.iterate_succ_apply]

private theorem recurrenceLift_spec (a : ℕ → W) (i : ℕ) :
    recurrenceLift p C a i - (p : W) * recurrenceLift p C a (i + 1) = a i := by
  let E (a : ℕ → W) (i : ℕ) := recurrenceLift p C a i -
    (p : W) * recurrenceLift p C a (i + 1) - a i
  have he (a : ℕ → W) (i : ℕ) : E a i = verschiebung (E (recurrenceTail p C a) i) := by
    change recurrenceLift p C a i - (p : W) * recurrenceLift p C a (i + 1) - a i =
      verschiebung (recurrenceLift p C (recurrenceTail p C a) i -
        (p : W) * recurrenceLift p C (recurrenceTail p C a) (i + 1) - recurrenceTail p C a i)
    rw [recurrenceLift_split p C a i, recurrenceLift_split p C a (i + 1), mul_add]
    have hpV (x : W) : verschiebung ((p : W) * x) = (p : W) * verschiebung x := by
      simp only [← nsmul_eq_mul, map_nsmul]
    rw [map_sub, map_sub, hpV, recurrenceTail_spec]
    abel
  have hz (j : ℕ) (a : ℕ → W) : (E a i).coeff j = 0 := by
    induction j generalizing a with
    | zero => rw [he, verschiebung_coeff_zero]
    | succ j hj => rw [he, verschiebung_coeff_succ, hj]
  have h : E a i = 0 := by ext j; rw [hz, zero_coeff]
  exact sub_eq_zero.mp h

/-- p 正則な p 進完備環の Witt 環は p 進完備。 -/
theorem witt_isAdicComplete
    (hpC : Function.Injective (fun x : C => (p : C) * x)) :
    IsAdicComplete (Ideal.span {(p : W)}) W := by
  apply (isAdicComplete_iff_adicRecurrenceMap_bijective_of_regular (M := W) (p : W)
    (witt_mul_prime_injective p C hpC)).mpr
  constructor
  · intro a b h
    funext i
    apply witt_ghostMap_injective_of_mul_prime_injective p C hpC
    funext j
    let g : W →+* C := ghostComponent j
    have hg : adicRecurrenceMap (M := C) (p : C) (g ∘ a) =
        adicRecurrenceMap (M := C) (p : C) (g ∘ b) := by
      funext k
      have hk : a k - (p : W) * a (k + 1) = b k - (p : W) * b (k + 1) := congrFun h k
      change g (a k) - (p : C) * g (a (k + 1)) = g (b k) - (p : C) * g (b (k + 1))
      simpa only [map_sub, map_mul, map_natCast] using congrArg g hk
    exact congrFun ((adicRecurrenceMap_bijective (M := C) (p : C)).injective hg) i
  · intro a
    exact ⟨recurrenceLift p C a, funext (recurrenceLift_spec p C a)⟩

end SerrePositivity.BhattScholze.Prismatic
