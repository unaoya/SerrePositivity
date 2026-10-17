module

public import SerrePositivity.BhattScholze.Andre.Transfinite.CountableCompletion
public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidCompletionColimit
open SerrePositivity.BhattScholze.Andre.Transfinite
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre.Transfinite
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
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j)
omit [Nonempty ι] in
include hbound in
/-- ## 概要
一段の元の可算族に関する等式が環余極限で成り立ち、可算添字集合が上界を持つなら、
すべての等式が同時に成り立つ後の段が存在する。
BS Thm 7.14（著者版 p.61）の非可算共終性の極限段を補足する。

## 方針
各等式が成り立つ段を環余極限の零の判定で選び、それらの可算集合に共通上界を取る。

## 規約
環と添字は Type u。素数性・p 正則性・完全平坦性・単射性を追加しない。

## 使われ方
ω₁ 塔の終段において、任意の両立する環遷移射について自動的完備性を得る。
-/
theorem exists_stage_countable_equalities {κ : Type v} [Countable κ] (i : ι) (a b : κ → R i)
    (hab : ∀ x, Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (a x) =
      Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (b x)) :
    ∃ j, ∃ hij : i ≤ j, ∀ x, f i j hij (a x) = f i j hij (b x) := by
  classical
  have hz (x : κ) : Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (a x - b x) = 0 := by
    rw [map_sub, hab, sub_self]
  choose j hij hj using (fun x ↦ Ring.DirectLimit.of.zero_exact (hz x))
  obtain ⟨k, hk⟩ := hbound (Set.range j) (Set.countable_range j)
  obtain ⟨l, hil, hkl⟩ := exists_ge_ge i k
  refine ⟨l, hil, fun x ↦ sub_eq_zero.mp ?_⟩
  have hjl : j x ≤ l := (hk (j x) ⟨x, rfl⟩).trans hkl
  have he := congrArg (f (j x) l hjl) (hj x)
  simpa only [map_sub, map_zero, DirectedSystem.map_map' f] using he


include hbound in
/-- ## 概要
各段が p 進完備な有向系で、可算添字集合がすべて上界を持つなら、
環余極限は p 進完備である。遷移射の単射性は不要。
BS Thm 7.14（著者版 p.61）の非可算共終性の極限段を補足する。

## 方針
分離性の冪割算の証人と、Cauchy 列の差の冪割算の証人を一段へ降ろす。
その後、可算個の等式も同時に後の段へ降ろし、そこで完備性を適用する。

## 規約
環と添字は Type u。素数性・p 正則性・完全平坦性・単射性を追加しない。

## 使われ方
ω₁ 塔の終段において、任意の両立する環遷移射について自動的完備性を得る。
-/
theorem isAdicComplete_directLimit_of_countable_upperBound_without_injective (p : ℕ)
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)] :
    IsAdicComplete (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  classical
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let ofL := Ring.DirectLimit.of R (fun i j h ↦ f i j h)
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
    have hdivL : ∀ n, ofL k (f i k hik x) =
        ofL k ((p : R k) ^ n * f j k hjk (d' n)) := by
      intro n
      simpa only [ofL, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f, hd'] using hd n
    obtain ⟨l, hkl, hl⟩ := exists_stage_countable_equalities R f hbound k
      (fun _ : ℕ ↦ f i k hik x) (fun n ↦ (p : R k) ^ n * f j k hjk (d' n)) hdivL
    have hz : f k l hkl (f i k hik x) = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : R l)}) (R l))
      intro n
      apply (principal_smodEq_iff (p : R l) _ 0 n).mpr
      refine ⟨f k l hkl (f j k hjk (d' n)), ?_⟩
      simpa only [sub_zero, map_mul, map_pow, map_natCast] using hl n
    rw [← Ring.DirectLimit.of_f hik x, ← Ring.DirectLimit.of_f hkl, hz, map_zero]
  · constructor
    intro a ha
    have hdiff : ∀ m n : ℕ, ∃ z : L, a m - a (m+n) = (p : L) ^ m * z := by
      intro m n
      exact (principal_smodEq_iff (p : L) (a m) (a (m+n)) m).mp (ha (Nat.le_add_right m n))
    choose d hd using hdiff
    obtain ⟨i, b, hb⟩ := exists_stage_countable_family R f hbound a
    obtain ⟨j, c, hc⟩ := exists_stage_countable_family R f hbound (Function.uncurry d)
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let b' : ℕ → R k := fun n ↦ f i k hik (b n)
    have heqL : ∀ mn : ℕ × ℕ, ofL k (b' mn.1 - b' (mn.1+mn.2)) =
        ofL k ((p : R k) ^ mn.1 * f j k hjk (c mn)) := by
      rintro ⟨m, n⟩
      simpa only [ofL, b', map_sub, map_mul, map_pow, map_natCast, Ring.DirectLimit.of_f,
        hb, hc, Function.uncurry_apply_pair] using hd m n
    obtain ⟨l, hkl, hl⟩ := exists_stage_countable_equalities R f hbound k
      (fun mn : ℕ × ℕ ↦ b' mn.1 - b' (mn.1+mn.2))
      (fun mn ↦ (p : R k) ^ mn.1 * f j k hjk (c mn)) heqL
    let b'' : ℕ → R l := fun n ↦ f k l hkl (b' n)
    have heq : ∀ m n, b'' m - b'' (m+n) =
        (p : R l) ^ m * f k l hkl (f j k hjk (c (m,n))) := by
      intro m n
      simpa only [b'', map_sub, map_mul, map_pow, map_natCast] using hl (m,n)
    obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : R l)}) b'' (by
      intro m n hmn
      apply (principal_smodEq_iff (p : R l) _ _ m).mpr
      refine ⟨f k l hkl (f j k hjk (c (m,n-m))), ?_⟩
      simpa only [Nat.add_sub_of_le hmn] using heq m (n-m))
    refine ⟨ofL l z, ?_⟩
    intro n
    obtain ⟨t, ht⟩ := (principal_smodEq_iff (p : R l) (b'' n) z n).mp (hz n)
    apply (principal_smodEq_iff (p : L) (a n) (ofL l z) n).mpr
    refine ⟨ofL l t, ?_⟩
    have he := congrArg (ofL l) ht
    simpa only [ofL, b'', b', map_sub, map_mul, map_pow, map_natCast,
      Ring.DirectLimit.of_f, hb] using he
include hbound in
/-- ## 概要
perfectoid 環の有向系で可算添字集合が上界を持つとき、環余極限自体が perfectoid となる。
BS Thm 7.14（著者版 p.61）の非可算共終性の極限段を補足する。

## 方針
遷移射の単射性なしで証明した自動的完備性を用い、標準完備化との環同型によって
完備化の perfectoid 性を未完備余極限に移す。

## 規約
最小元を持つ有向添字を用いる。p 完全平坦性・単射性・p 正則性は要求しない。
零環を許す。環と添字は Type u。

## 使われ方
ω₁ 反復の終段で、根の存在を保った未完備余極限を perfectoid 環として使う。
-/
theorem isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound_without_flatness
    [OrderBot ι] (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, SerrePositivity.IsIntegralPerfectoid (R i) p) :
    SerrePositivity.IsIntegralPerfectoid (Ring.DirectLimit R (fun i j h ↦ f i j h)) p := by
  have hc (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := by
    rcases hR i with hz | ⟨_, hc, _⟩
    · let := hz
      infer_instance
    · exact hc
  let (i : ι) : IsAdicComplete (Ideal.span {(p : R i)}) (R i) := hc i
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let := isAdicComplete_directLimit_of_countable_upperBound_without_injective R f hbound p
  exact isIntegralPerfectoid_of_ringEquiv p
    (AdicCompletion.ofAlgEquiv (Ideal.span {(p : L)})).symm.toRingEquiv
    (isIntegralPerfectoid_adicCompletion_ringDirectLimit R f hR)

end SerrePositivity.BhattScholze.Andre.Transfinite
