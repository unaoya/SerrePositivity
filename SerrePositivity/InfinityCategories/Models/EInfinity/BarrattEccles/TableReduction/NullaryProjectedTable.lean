module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullaryForwardSchedule
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OutputTraceUniqueness

/-!
模型。文献の定義との比較は後で
# 空語合成の射影選択行列の一意性

概要：Berger–Fresse §1.5.7–9 の指定値削除で、同じ成功出力から同じ射影選択行を得る。
方針：各射影表を実際の合成 Schedule に包装し、成功出力の行長一意性を使う。
規約：元の選択行列は実際の抽出証跡を持ち、指定値は一出現。
使われ方：射影選択行から元の成功出力を戻す一般比較の入力。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：同じ行数の射影表の選択長は射影した選択行の長さ（BF §1.5.7）。
方針：行と選択語の同時帰納法で zipWith の全行を比較する。
規約：射影後の選択が空の場合も等式自体は成立する。
使われ方：同じ射影表から射影した選択行列の行長を揃える。 -/
lemma filterMapRows_snd {α β : Type*} (f : α → Option β)
    (rows : List (List α × ℕ)) (picked : List (List α))
    (hl : rows.length = picked.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows f rows picked).map Prod.snd =
      (picked.map (List.filterMap f)).map List.length := by
  induction rows generalizing picked with
  | nil => cases picked <;> simp_all [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows]
  | cons row rows ih =>
    cases picked with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons word picked =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows, List.zipWith_cons_cons, List.map_cons]
      exact congrArg ((word.filterMap f).length :: ·) (ih picked hl)

/-- 概要：元の一出現成功表は nullary 射影の保持条件を満たす（BF §1.5.7–9）。
方針：削除後の正の語長と全行末再出現を実際の抽出証跡から得る。
規約：出力 arity は正。削除後の非退化性は要求しない。
使われ方：射影表の成功と元の成功語の一意性の共通入力。 -/
lemma nullary_trace_ready {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d) (picked : List (List (Fin (m + 1))))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] picked) (hc : picked.flatten.count k = 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapReady (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) picked := by
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten).length = m + d := by
    have h1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord_length k picked.flatten
    have h2 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w s picked.flatten ht.reduceRows
    omega
  have ho : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten ≠ [] := by
    intro he
    rw [he, List.length_nil] at hl
    omega
  have hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_length picked (ht.separatedRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w s)) ht.nonempty
    rw [ht.length]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, Nat.add_sub_cancel]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w s picked.flatten ht.reduceRows
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_eraseSlotWord_ready k picked hr ht.nonempty (by omega) ho

/-- 概要：一出現の実際の射影表は合成列の本来の Schedule の表（BF §1.5.7–9）。
方針：行末再出現で全抽出を射影し、実際の逆行列と削除後の長さで包装する。
規約：元の選択語の証跡をそのまま使う。
使われ方：二つの射影選択行列を同じ成功 Schedule へ比較する。 -/
lemma nullary_projected_table_schedule {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d) (picked : List (List (Fin (m + 1))))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] picked) (hc : picked.flatten.count k = 1) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 0) d,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m 0 k (w j) τ) r =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) picked ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m 0 k (w j) τ) r) [] =
        some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten) := by
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten).length = m + d := by
    have h1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord_length k picked.flatten
    have h2 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w s picked.flatten ht.reduceRows
    omega
  have hnonempty : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten ≠ [] := by
    intro he
    rw [he, List.length_nil] at hl
    omega
  have hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_of_length picked (ht.separatedRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w s)) ht.nonempty
    rw [ht.length]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, Nat.add_sub_cancel]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w s picked.flatten ht.reduceRows
  have hready := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentEnds_eraseSlotWord_ready k picked hr ht.nonempty
    (by omega) hnonempty
  have hp := ht.filterMap_reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel_partial_injective k)
    hready
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) picked) [] =
    some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten) at hp
  have hmatrix : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) picked).map Prod.fst =
      List.ofFn (fun j => List.ofFn (permutationComposition m 0 k (w j) τ).symm) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows_fst _ _ _ ht.length.symm]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, Function.comp_def]
    apply congrArg List.ofFn
    funext i
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row_nullary (w i) τ k).symm
  have hsum : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) picked).map Prod.snd).sum =
      m + 0 + d := by
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_length _ _ _ hp, hl]
    rfl
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_of_table _ _ _ hp hmatrix hsum
  exact ⟨r, hr, by rw [hr]; exact hp⟩

/-- 概要：同じ削除出力を持つ二つの元の成功表の射影選択行は一致（BF §1.5.7–9）。
方針：射影表を同じ合成 Schedule に揃え、平坦化と各行長の等式を使う。
規約：元の成功 Schedule は異なってよく、出力 arity は正。
使われ方：空語合成の成功項の単射性のための射影行列一致。 -/
lemma nullary_projected_selected_eq {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (s s' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d)
    (picked picked' : List (List (Fin (m + 1))))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] picked) (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s') [] picked')
    (hc : picked.flatten.count k = 1) (hc' : picked'.flatten.count k = 1)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked'.flatten) :
    picked.map (List.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k)) =
      picked'.map (List.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k)) := by
  obtain ⟨r, hr, hs⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_projected_table_schedule hm w τ k s picked h hc
  obtain ⟨r', hr', hs'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_projected_table_schedule hm w τ k s' picked' h' hc'
  have hrr : r = r' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_list _ _ r r' _ hs (by rw [he]; exact hs')
  subst r'
  apply List.eq_iff_flatten_eq.mpr
  refine ⟨?_, ?_⟩
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, List.filterMap_flatten] using he
  · rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows_snd _ _ _ h.length.symm, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows_snd _ _ _ h'.length.symm,
      ← hr, ← hr']

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
