module

public import SerrePositivity.AlgebraicGeometry.ChartAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：KST §5、Stacks Lemma 31.35.5 の境界外の開閉分割の分母消去。
方針：局所化環の冪等元の分母を払い、直交する二つの境界内の元を選ぶ。
規約：境界元の正則性により局所化の単射性を使う。
使われ方：一般階数の開閉部分を blowup のチャートに分離する中心を作る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R]

/--
概要：境界外の冪等元は互いに積が零の二つの境界内の元を与える。
方針：冪等元の分母を払い、さらに境界元を一回掛け、直交性を局所化で判定する。
規約：KST §5、Stacks Lemma 31.35.5、指数は正である。
使われ方：境界外の二つの開閉部分を分離する有限生成中心。
-/
theorem exists_orthogonal_boundary_numerators (f : R) (hf : IsRegular f)
    (e : Localization.Away f) (he : IsIdempotentElem e) :
    ∃ (N : ℕ) (a b : R), 0 < N ∧ f ∣ a ∧ f ∣ b ∧
      a + b = f ^ N ∧ a * b = 0 ∧
      algebraMap R (Localization.Away f) a =
        e * (algebraMap R (Localization.Away f) f) ^ N := by
  let F := Localization.Away f
  let φ : R →+* F := algebraMap R F
  have hφ : Function.Injective φ :=
    IsLocalization.injective F (Submonoid.powers_le.mpr
      (isRegular_iff_mem_nonZeroDivisors.mp hf))
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f e
  refine ⟨n + 1, a * f, f ^ (n + 1) - a * f, Nat.succ_pos n, ?_, ?_, ?_, ?_, ?_⟩
  · exact dvd_mul_left f a
  · exact dvd_sub (dvd_pow_self f (Nat.succ_ne_zero n)) (dvd_mul_left f a)
  · ring
  · apply hφ
    have ha' : φ a = e * φ f ^ n := ha.symm
    simp only [map_mul, map_sub, map_pow, map_zero, ha', pow_succ]
    calc
      _ = (e - e * e) * (φ f ^ n * φ f) ^ 2 := by ring
      _ = 0 := by rw [he.eq, sub_self, zero_mul]
  · change φ (a * f) = _
    rw [map_mul, ← ha, pow_succ, mul_assoc]

/--
概要：チャート中心元と積が零の元の像は、その実際の blowup チャート内で零。
方針：チャート中心元の非零因子性で積の等式を打ち消す。
規約：KST §5、Stacks Lemma 31.35.5、元の環で中心元が正則である必要はない。
使われ方：直交中心の相手側がチャートから消えることを示す。
-/
theorem chartBaseMap_eq_zero_of_mul_eq_zero (I : Ideal R) (a : I) (b : R)
    (hab : a.val * b = 0) : chartBaseMap I a b = 0 := by
  apply (mem_nonZeroDivisors_iff_left.mp (chartBaseMap_mem_nonZeroDivisors I a))
  rw [← map_mul, hab, map_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
