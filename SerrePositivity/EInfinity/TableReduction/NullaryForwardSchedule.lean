module

public import SerrePositivity.EInfinity.TableReduction.NullaryRetainedEnds
public import SerrePositivity.EInfinity.TableReduction.NullaryScheduleExtension
public import SerrePositivity.EInfinity.TableReduction.SuccessfulWords

/-!
# 一出現の指定値削除による nullary の順方向成功

概要：Berger–Fresse §1.5.7–9 の元の成功表を指定値削除した実際の合成表へ射影する。
方針：行末の再出現から部分射影の条件を満たし、同じ全行列と削除後の語長で包装する。
規約：指定値は一回、出力 arity は正。退化する削除出力も許す。
使われ方：nullary 次数零の元の成功項から目標の成功 Schedule を構成する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection BarrattEccles

/-- 概要：一出現の指定値を削除した元の成功表は実際の nullary 合成表で成功（BF §1.5.7–9）。
方針：再出現する行末を保持して全表を射影し、元の合成逆行列と正しい総和にまとめる。
規約：出力 arity は正で、削除出力の非退化性は要求しない。
使われ方：nullary の順方向の成功項を構成する。 -/
lemma nullary_forward_schedule {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (s : Schedule (m + 1) d) (out : List (Fin (m + 1)))
    (h : reduceRows (rows w s) [] = some out) (hc : out.count k = 1) :
    ∃ r : Schedule (m + 0) d,
      reduceRows (rows (fun j => permutationComposition m 0 k (w j) τ) r) [] =
        some (eraseSlotWord k out) := by
  have hl : (eraseSlotWord k out).length = m + d := by
    have h1 := eraseSlotWord_length k out
    have h2 := output_length w s out h
    omega
  have hnonempty : eraseSlotWord k out ≠ [] := by
    intro he
    rw [he, List.length_nil] at hl
    omega
  obtain ⟨picked, ht, he⟩ := extractionTrace_of_reduceRows _ _ _ h
  have hr : RecurrentEnds picked := by
    apply recurrentEnds_of_length picked (ht.separatedRows (rows_nodup w s)) ht.nonempty
    rw [he, ht.length]
    simp only [rows, List.length_ofFn, Nat.add_sub_cancel]
    exact output_length w s out h
  have hready := recurrentEnds_eraseSlotWord_ready k picked hr ht.nonempty
    (by rw [he, hc]) (by rw [he]; exact hnonempty)
  have hp := ht.filterMap_reduceRows (eraseSlotLabel k) (eraseSlotLabel_partial_injective k)
    hready
  change reduceRows (filterMapRows (eraseSlotLabel k) (rows w s) picked) [] =
    some (eraseSlotWord k picked.flatten) at hp
  rw [he] at hp
  have hmatrix : (filterMapRows (eraseSlotLabel k) (rows w s) picked).map Prod.fst =
      List.ofFn (fun j => List.ofFn (permutationComposition m 0 k (w j) τ).symm) := by
    rw [filterMapRows_fst _ _ _ ht.length.symm]
    simp only [rows, List.map_ofFn, Function.comp_def]
    apply congrArg List.ofFn
    funext i
    exact (permutationComposition_inverse_row_nullary (w i) τ k).symm
  have hsum : ((filterMapRows (eraseSlotLabel k) (rows w s) picked).map Prod.snd).sum =
      m + 0 + d := by
    rw [← reduceRows_length _ _ _ hp, hl]
    rfl
  obtain ⟨r, hr⟩ := schedule_of_table _ _ _ hp hmatrix hsum
  exact ⟨r, by rw [hr]; exact hp⟩

/-- 概要：削除後が非退化なら元の成功基底語は実際の目標成功基底語へ写る（BF §1.5.7–9）。
方針：順方向成功の Schedule と非退化性を本来の次数の BasisWord にまとめる。
規約：正の出力 arity と指定値一出現。
使われ方：成功基底語の有限対応の順方向存在。 -/
lemma nullary_successfulWord_forward_exists {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (p : SuccessfulWord w) (hc : occurrenceCount p.val.2.val k = 1)
    (hne : (eraseSlotWord k (List.ofFn p.val.2.val)).IsChain (· ≠ ·)) :
    ∃ q : SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ),
      List.ofFn q.val.2.val = eraseSlotWord k (List.ofFn p.val.2.val) := by
  obtain ⟨r, hr⟩ := nullary_forward_schedule hm w τ k p.val.1 _ p.property hc
  obtain ⟨v, hv⟩ := word_exists_of_success _ r _ hr hne
  exact ⟨⟨(r, v), by rw [hv]; exact hr⟩, hv⟩

end SerrePositivity.EInfinity.TableReduction
