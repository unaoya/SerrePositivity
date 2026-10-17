module

public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableDescent
public import Mathlib.RingTheory.AdicCompletion.Basic
universe u
/-! # 非可算共終性をもつ有向余極限の p 進完備性

BS Thm 7.14（著者版 p.61）の超限反復の極限段に必要な一般論。
可算集合の上界と単射な遷移写像から、完備化を挟まず余極限の完備性を示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze.Andre.Transfinite

/-- 主イデアル進合同は差の冪倍表示と同値。
BS Thm 7.14（著者版 p.61）の極限段の補助計算として、合同を有限代数的な等式へ直す。 -/
private lemma principal_smodEq_iff {S : Type*} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule S S))] ↔
      ∃ z, x - y = a ^ n * z := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  rfl

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (p : ℕ)
local notation "L" => Ring.DirectLimit R (fun i j h ↦ f i j h)
local notation "ofL" => Ring.DirectLimit.of R (fun i j h ↦ f i j h)
/-- ## 概要
任意の可算添字集合が上界を持つ有向系で、遷移写像が単射かつ各段が p 進完備なら、
有向余極限も p 進完備である。BS Thm 7.14（著者版 p.61）の極限段の補助命題。

## 方針
分離性では全ての p 冪の割り算の証人を、前完備性では Cauchy 列と差の割り算の証人を、
可算データの降下により一段へ移す。その段から余極限への単射性で等式を反映する。

## 規約
p は任意の自然数でよく、素数性・p 正則性・非零性は不要。
環と塔の添字は Type u に留める。単射性を完全忠実平坦性から導く工程は別。

## 使われ方
非可算共終性の極限段と ω₁ の終段で、和集合の自動的な p 進完備性を検証する。
可算共終性の極限段の完備化はこの命題の対象外。
-/
theorem isAdicComplete_directLimit_of_countable_upperBound
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j)
    (hf : ∀ i j h, Function.Injective (f i j h))
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)] :
    IsAdicComplete (Ideal.span {(p : L)}) L := by
  classical
  rw [isAdicComplete_iff]
  constructor
  · constructor
    intro x hx
    have hx' : ∀ n : ℕ, ∃ z : L, x = (p : L) ^ n * z := by
      intro n
      simpa only [sub_zero] using (principal_smodEq_iff (p : L) x 0 n).mp (hx n)
    choose d hd using hx'
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨j, d', hd'⟩ := exists_stage_countable_family R f hbound d
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hdiv : ∀ n, f i k hik x = (p : R k) ^ n * f j k hjk (d' n) := by
      intro n
      apply Ring.DirectLimit.of_injective f hf k
      simpa only [map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f, hd'] using hd n
    have hz : f i k hik x = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : R k)}) (R k))
      intro n
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        sub_zero, Ideal.mem_span_singleton]
      exact ⟨f j k hjk (d' n), hdiv n⟩
    rw [← Ring.DirectLimit.of_f hik x, hz, map_zero]
  · constructor
    intro a ha
    have hdiff : ∀ m n : ℕ, ∃ z : L, a m - a (m + n) = (p : L) ^ m * z := by
      intro m n
      exact (principal_smodEq_iff (p : L) (a m) (a (m+n)) m).mp (ha (Nat.le_add_right m n))
    choose d hd using hdiff
    obtain ⟨i, b, hb⟩ := exists_stage_countable_family R f hbound a
    obtain ⟨j, c, hc⟩ := exists_stage_countable_family R f hbound (Function.uncurry d)
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let b' : ℕ → R k := fun n ↦ f i k hik (b n)
    have heq : ∀ m n, b' m - b' (m+n) = (p : R k) ^ m * f j k hjk (c (m,n)) := by
      intro m n
      apply Ring.DirectLimit.of_injective f hf k
      simpa only [b', map_sub, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f,
        hb, hc, Function.uncurry_apply_pair] using hd m n
    obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : R k)}) b' (by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      refine ⟨f j k hjk (c (m,n-m)), ?_⟩
      simpa only [Nat.add_sub_of_le hmn] using heq m (n-m))
    refine ⟨ofL k z, ?_⟩
    intro n
    obtain ⟨t, ht⟩ : ∃ t, b' n - z = (p : R k)^n * t := by
      have hmem := (SModEq.sub_mem).mp (hz n)
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at hmem
      exact Ideal.mem_span_singleton.mp hmem
    apply (principal_smodEq_iff (p : L) (a n) (ofL k z) n).mpr
    refine ⟨ofL k t, ?_⟩
    have he := congrArg (ofL k) ht
    simpa only [b', map_sub, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f, hb] using he
end SerrePositivity.BhattScholze.Andre.Transfinite
