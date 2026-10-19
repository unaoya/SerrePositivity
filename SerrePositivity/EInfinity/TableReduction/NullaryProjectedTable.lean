module

public import SerrePositivity.EInfinity.TableReduction.NullaryForwardSchedule
public import SerrePositivity.EInfinity.TableReduction.OutputTraceUniqueness

/-!
# 空語合成の射影選択行列の一意性

概要：Berger–Fresse §1.5.7–9 の指定値削除で、同じ成功出力から同じ射影選択行を得る。
方針：各射影表を実際の合成 Schedule に包装し、成功出力の行長一意性を使う。
規約：元の選択行列は実際の抽出証跡を持ち、指定値は一出現。
使われ方：射影選択行から元の成功出力を戻す一般比較の入力。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection BarrattEccles

/-- 概要：同じ行数の射影表の選択長は射影した選択行の長さ（BF §1.5.7）。
方針：行と選択語の同時帰納法で zipWith の全行を比較する。
規約：射影後の選択が空の場合も等式自体は成立する。
使われ方：同じ射影表から射影した選択行列の行長を揃える。 -/
lemma filterMapRows_snd {α β : Type*} (f : α → Option β)
    (rows : List (List α × ℕ)) (picked : List (List α))
    (hl : rows.length = picked.length) :
    (filterMapRows f rows picked).map Prod.snd =
      (picked.map (List.filterMap f)).map List.length := by
  induction rows generalizing picked with
  | nil => cases picked <;> simp_all [filterMapRows]
  | cons row rows ih =>
    cases picked with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons word picked =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [filterMapRows, List.zipWith_cons_cons, List.map_cons]
      exact congrArg ((word.filterMap f).length :: ·) (ih picked hl)

/-- 概要：元の一出現成功表は nullary 射影の保持条件を満たす（BF §1.5.7–9）。
方針：削除後の正の語長と全行末再出現を実際の抽出証跡から得る。
規約：出力 arity は正。削除後の非退化性は要求しない。
使われ方：射影表の成功と元の成功語の一意性の共通入力。 -/
lemma nullary_trace_ready {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (s : Schedule (m + 1) d) (picked : List (List (Fin (m + 1))))
    (ht : ExtractionTrace (rows w s) [] picked) (hc : picked.flatten.count k = 1) :
    FilterMapReady (eraseSlotLabel k) picked := by
  have hl : (eraseSlotWord k picked.flatten).length = m + d := by
    have h1 := eraseSlotWord_length k picked.flatten
    have h2 := output_length w s picked.flatten ht.reduceRows
    omega
  have ho : eraseSlotWord k picked.flatten ≠ [] := by
    intro he
    rw [he, List.length_nil] at hl
    omega
  have hr : RecurrentEnds picked := by
    apply recurrentEnds_of_length picked (ht.separatedRows (rows_nodup w s)) ht.nonempty
    rw [ht.length]
    simp only [rows, List.length_ofFn, Nat.add_sub_cancel]
    exact output_length w s picked.flatten ht.reduceRows
  exact recurrentEnds_eraseSlotWord_ready k picked hr ht.nonempty (by omega) ho

/-- 概要：一出現の実際の射影表は合成列の本来の Schedule の表（BF §1.5.7–9）。
方針：行末再出現で全抽出を射影し、実際の逆行列と削除後の長さで包装する。
規約：元の選択語の証跡をそのまま使う。
使われ方：二つの射影選択行列を同じ成功 Schedule へ比較する。 -/
lemma nullary_projected_table_schedule {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (s : Schedule (m + 1) d) (picked : List (List (Fin (m + 1))))
    (ht : ExtractionTrace (rows w s) [] picked) (hc : picked.flatten.count k = 1) :
    ∃ r : Schedule (m + 0) d,
      rows (fun j => permutationComposition m 0 k (w j) τ) r =
        filterMapRows (eraseSlotLabel k) (rows w s) picked ∧
      reduceRows (rows (fun j => permutationComposition m 0 k (w j) τ) r) [] =
        some (eraseSlotWord k picked.flatten) := by
  have hl : (eraseSlotWord k picked.flatten).length = m + d := by
    have h1 := eraseSlotWord_length k picked.flatten
    have h2 := output_length w s picked.flatten ht.reduceRows
    omega
  have hnonempty : eraseSlotWord k picked.flatten ≠ [] := by
    intro he
    rw [he, List.length_nil] at hl
    omega
  have hr : RecurrentEnds picked := by
    apply recurrentEnds_of_length picked (ht.separatedRows (rows_nodup w s)) ht.nonempty
    rw [ht.length]
    simp only [rows, List.length_ofFn, Nat.add_sub_cancel]
    exact output_length w s picked.flatten ht.reduceRows
  have hready := recurrentEnds_eraseSlotWord_ready k picked hr ht.nonempty
    (by omega) hnonempty
  have hp := ht.filterMap_reduceRows (eraseSlotLabel k) (eraseSlotLabel_partial_injective k)
    hready
  change reduceRows (filterMapRows (eraseSlotLabel k) (rows w s) picked) [] =
    some (eraseSlotWord k picked.flatten) at hp
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
  exact ⟨r, hr, by rw [hr]; exact hp⟩

/-- 概要：同じ削除出力を持つ二つの元の成功表の射影選択行は一致（BF §1.5.7–9）。
方針：射影表を同じ合成 Schedule に揃え、平坦化と各行長の等式を使う。
規約：元の成功 Schedule は異なってよく、出力 arity は正。
使われ方：空語合成の成功項の単射性のための射影行列一致。 -/
lemma nullary_projected_selected_eq {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (s s' : Schedule (m + 1) d)
    (picked picked' : List (List (Fin (m + 1))))
    (h : ExtractionTrace (rows w s) [] picked) (h' : ExtractionTrace (rows w s') [] picked')
    (hc : picked.flatten.count k = 1) (hc' : picked'.flatten.count k = 1)
    (he : eraseSlotWord k picked.flatten = eraseSlotWord k picked'.flatten) :
    picked.map (List.filterMap (eraseSlotLabel k)) =
      picked'.map (List.filterMap (eraseSlotLabel k)) := by
  obtain ⟨r, hr, hs⟩ := nullary_projected_table_schedule hm w τ k s picked h hc
  obtain ⟨r', hr', hs'⟩ := nullary_projected_table_schedule hm w τ k s' picked' h' hc'
  have hrr : r = r' := schedule_eq_of_same_list _ _ r r' _ hs (by rw [he]; exact hs')
  subst r'
  apply List.eq_iff_flatten_eq.mpr
  refine ⟨?_, ?_⟩
  · simpa only [eraseSlotWord, List.filterMap_flatten] using he
  · rw [← filterMapRows_snd _ _ _ h.length.symm, ← filterMapRows_snd _ _ _ h'.length.symm,
      ← hr, ← hr']

end SerrePositivity.EInfinity.TableReduction
