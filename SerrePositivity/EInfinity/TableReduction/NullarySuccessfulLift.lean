module

public import SerrePositivity.EInfinity.TableReduction.NullaryScheduleExtension
public import SerrePositivity.EInfinity.TableReduction.SuccessfulWords
public import SerrePositivity.EInfinity.Surjection.NullaryWordLifting
public import SerrePositivity.EInfinity.Surjection.DegreeZero

/-!
# 空語合成の成功基底語の逆向き持ち上げ

概要：Berger–Fresse §1.5.7–9 の実際の nullary 成功基底語を元の成功基底語へ持ち上げる。
方針：一行延長の Schedule と非退化語を構成し、成功の被覆性で BasisWord にまとめる。
規約：元の指定値は一出現であり、空語との χ 合成は目標の基底元を与える。
使われ方：nullary 次数零の成功項の有限全単射の逆向き存在。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.TableReduction

open Surjection BarrattEccles

/-- 概要：実際の nullary 成功基底語は元の指定値一出現の成功基底語の削除（BF §1.5.7–9）。
方針：解放値探索の成功 Schedule と削除後から戻した非退化性で元の基底語を作る。
規約：目標・元の Schedule と基底語は本来の次数を保つ。
使われ方：成功項対応の逆向きの存在を与える。 -/
lemma nullary_successfulWord_lift_exists {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1))
    (q : SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ)) :
    ∃ p : SuccessfulWord w, occurrenceCount p.val.2.val k = 1 ∧
      eraseSlotWord k (List.ofFn p.val.2.val) = List.ofFn q.val.2.val := by
  obtain ⟨s, pre, post, hp, hpost, hout, hs⟩ :=
    nullary_success_schedule w τ k q.val.1 (List.ofFn q.val.2.val) q.property
  have hc : (eraseSlotWord k (pre ++ post)).IsChain (· ≠ ·) := by
    rw [← hout]
    exact isChain_ofFn_of_nondegenerate q.val.2.val q.val.2.nondegenerate
  obtain ⟨v, hv⟩ := word_exists_of_success w s (pre ++ k :: post) hs
    (isChain_insert_of_eraseSlotWord k pre post hp hpost hc)
  refine ⟨⟨(s, v), by rw [hv]; exact hs⟩, ?_, ?_⟩
  · change (List.ofFn v.val).count k = 1
    rw [hv, List.count_append, List.count_cons_self]
    simp [List.count_eq_zero.mpr hp, List.count_eq_zero.mpr hpost]
  · rw [hv, eraseSlotWord_insert, ← hout]

/-- 概要：持ち上げた元の成功基底語と空語との χ 合成は目標基底元（BF §1.2.4・§1.5.7–9）。
方針：一出現の空語合成を削除語に同定し、実際の目標語へ移す。
規約：任意の可換環と本来の全次数。
使われ方：逆向き対応で各有限和の項の値を保存する。 -/
lemma nullary_successfulWord_lift_term (A : Type u) [CommRing A] {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1))
    (q : SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ)) :
    ∃ p : SuccessfulWord w, occurrenceCount p.val.2.val k = 1 ∧
      compositionOnWords A p.val.2 (permutationWord (1 : Equiv.Perm (Fin 0))) k =
        basis A (m + 0) (d + 0) (ULift.up q.val.2) := by
  obtain ⟨p, hc, he⟩ := nullary_successfulWord_lift_exists w τ k q
  refine ⟨p, hc, ?_⟩
  rw [compositionOnWords_nullary_of_count_eq_one A _ _ _ hc, he,
    listGenerator_ofFn, generator_word]

end SerrePositivity.EInfinity.TableReduction
