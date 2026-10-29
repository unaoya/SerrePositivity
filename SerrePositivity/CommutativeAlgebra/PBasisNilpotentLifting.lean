module

public import SerrePositivity.FieldTheory.PBasis
public import SerrePositivity.CommutativeAlgebra.NilpotentFrobenius
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # p-basis の像を指定した持ち上げの一意性

このファイルは一意性を証明する。指定像を持つ写像の存在は別途実構成する。
-/

@[expose] public section
namespace SerrePositivity

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [CharP A p]
variable {ι : Type*} {b : ι → k}

/-- 核を一つの Frobenius 冪が消す場合、p-basis の像と剰余写像が持ち上げを決定する。 -/
theorem IsPBasis.ringHom_lift_unique_of_frobenius_kernel (hb : IsPBasis k p b)
    (f : A →+* B) (n : ℕ) (hkill : ∀ x, f x = 0 → x ^ p ^ n = 0)
    (l₁ l₂ : k →+* A) (hres : f.comp l₁ = f.comp l₂)
    (hbmap : ∀ i, l₁ (b i) = l₂ (b i)) : l₁ = l₂ := by
  apply hb.ringHom_ext_of_eq_pow_exp l₁ l₂ hbmap n
  intro x
  have hx : f (l₁ x - l₂ x) = 0 := by
    rw [map_sub, show f (l₁ x) = f (l₂ x) from RingHom.congr_fun hres x, sub_self]
  have hz := hkill (l₁ x - l₂ x) hx
  rw [sub_pow_expChar_pow] at hz
  simpa only [map_pow] using sub_eq_zero.mp hz

/-- 冪零核の場合の指定 p-basis 持ち上げの一意性。全射性・局所性は不要。 -/
theorem IsPBasis.ringHom_lift_unique_of_nilpotent_kernel (hb : IsPBasis k p b)
    (f : A →+* B) (hker : IsNilpotent (RingHom.ker f))
    (l₁ l₂ : k →+* A) (hres : f.comp l₁ = f.comp l₂)
    (hbmap : ∀ i, l₁ (b i) = l₂ (b i)) : l₁ = l₂ := by
  obtain ⟨n, hn⟩ := exists_pow_exp_eq_zero_of_nilpotent_ideal p (RingHom.ker f) hker
  exact hb.ringHom_lift_unique_of_frobenius_kernel f n (fun x hx ↦ hn x hx) l₁ l₂ hres hbmap

/-- 核について分離なら、剰余写像と指定p-basisの像が持ち上げを一意に決める。
存在に必要な完備性・全射性・局所性を一意性には要求しない。 -/
theorem IsPBasis.ringHom_lift_unique_of_hausdorff_kernel (hb : IsPBasis k p b)
    (f : A →+* B) [IsHausdorff (RingHom.ker f) A]
    (l₁ l₂ : k →+* A) (hres : f.comp l₁ = f.comp l₂)
    (hbmap : ∀ i, l₁ (b i) = l₂ (b i)) : l₁ = l₂ := by
  let I := RingHom.ker f
  ext x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have he := hb.ringHom_ext_of_eq_pow_exp
      ((Ideal.Quotient.mk (I ^ (n + 1))).comp l₁)
      ((Ideal.Quotient.mk (I ^ (n + 1))).comp l₂)
      (fun i ↦ congrArg (Ideal.Quotient.mk (I ^ (n + 1))) (hbmap i))
      (n + 1) (fun y ↦ ?_)
    · have hx := RingHom.congr_fun he x
      simpa only [smul_eq_mul, Ideal.mul_top] using
        (SModEq.sub_mem.mpr (Ideal.Quotient.eq.mp hx) :
          l₁ x ≡ l₂ x [SMOD I ^ (n + 1)])
    · apply Ideal.Quotient.eq.mpr
      change l₁ (y ^ p ^ (n + 1)) - l₂ (y ^ p ^ (n + 1)) ∈ I ^ (n + 1)
      rw [map_pow, map_pow, ← sub_pow_expChar_pow]
      have hy : l₁ y - l₂ y ∈ I := by
        change f (l₁ y - l₂ y) = 0
        rw [map_sub, show f (l₁ y) = f (l₂ y) from RingHom.congr_fun hres y, sub_self]
      exact Ideal.pow_le_pow_right (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
        (Ideal.pow_mem_pow hy _)

end SerrePositivity
