module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapseConcatenation
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapsePrefixes

/-!
模型。文献の定義との比較は後で
# 全除外も許した同じ行の抽出証跡

概要：Berger–Fresse §1.5.8 の内側射影で生じる全除外と末尾保持を一つに扱う。
方針：選択長 r と消費長 c を分け、c ≤ r ≤ c+1 の状態更新を記録する。
規約：選択が空の段も許す。元の TR の成功概念は変更しない。
使われ方：同じ内側置換の水平区間を、共有端点の有無を保って一行へまとめる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ行の先頭を全消費または末尾だけ残して抽出する証跡（BF §1.5.8）。
方針：消費する先頭長を明示して実際の除外リストを次段へ渡す。
規約：空選択では消費も零。正の末尾保持だけが通常の TR 一行に対応する。
使われ方：外側末尾が消える内側射影と空の内側選択を同時に記録する。 -/
inductive ConsumptionPrefix (row : List α) : List α → List α → List α → Prop
  | nil (removed : List α) : ConsumptionPrefix row removed [] removed
  | cons {removed out finish : List α} (r c : ℕ)
      (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length) (hc : c ≤ r) (hg : r ≤ c + 1)
      (tail : ConsumptionPrefix row (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take c) out finish) :
      ConsumptionPrefix row removed ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ out) finish

/-- 概要：同じ行の二段の選択は縮約後に一つの先頭部分となる（BF §1.5.8）。
方針：全消費では take_add、末尾保持では共有端点の縮約を使う。
規約：二段目の選択が空の場合も含め、選択長は max r (c+s)。
使われ方：水平区間を畳み込む帰納の出力側。 -/
lemma collapse_consumption_pair (xs : List α) (hn : xs.Nodup) (r c s : ℕ)
    (hr : r ≤ xs.length) (hc : c ≤ r) (hg : r ≤ c + 1)
    (hs : s ≤ (xs.drop c).length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take r ++ (xs.drop c).take s) = xs.take (max r (c + s)) := by
  by_cases he : r = c
  · subst r
    rw [← List.take_add, Nat.max_eq_right (by omega)]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ ((hn.take).isChain)
  · have he : r = c + 1 := by omega
    subst r
    cases s with
    | zero =>
      simp only [List.take_zero, List.append_nil, Nat.add_zero,
        Nat.max_eq_left (show c ≤ c + 1 by omega)]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ ((hn.take).isChain)
    | succ s =>
      have htotal : c + (s + 1) ≤ xs.length := by
        simp only [List.length_drop] at hs
        omega
      have hb : c + 1 ≤ (xs.take (c + (s + 1))).length := by
        rw [List.length_take, Nat.min_eq_left htotal]
        omega
      have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_overlap_take (xs.take (c + (s + 1))) (c + 1) (by omega) hb
      simp only [List.take_take, Nat.min_eq_left (show c + 1 ≤ c + (s + 1) by omega),
        Nat.add_sub_cancel, List.drop_take, Nat.add_sub_cancel_left] at hp
      rw [Nat.max_eq_right (show c + 1 ≤ c + (s + 1) by omega)]
      exact hp.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ ((hn.take).isChain))

/-- 概要：同じ行の消費証跡全体を一つの選択長・消費長へまとめる（BF §1.5.8）。
方針：後続の集約を drop で元の行へ戻し、二段の縮約と take_add で融合する。
規約：終状態はリストとして厳密に保持し、選択零の水平成分も許す。
使われ方：内側復元で水平成分全体を一つの元の内側行に戻す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix.normalize {row removed out finish : List α}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix row removed out finish) (hn : row.Nodup) :
    ∃ r c : ℕ, r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length ∧ c ≤ r ∧ r ≤ c + 1 ∧
      finish = removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take c ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r := by
  induction h with
  | nil removed => exact ⟨0, 0, by omega, by omega, by omega, by simp, rfl⟩
  | @cons removed out finish r c hb hc hg ht ih =>
    obtain ⟨s, t, hbs, hts, hsg, hfinish, hout⟩ := ih
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn] at hbs hfinish hout
    have hct : c + t ≤ max r (c + s) := by omega
    have hgap : max r (c + s) ≤ c + t + 1 := by omega
    have hbound : max r (c + s) ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by
      simp only [List.length_drop] at hbs
      omega
    refine ⟨max r (c + s), c + t, hbound, hct, hgap, ?_, ?_⟩
    · rw [hfinish, List.append_assoc, ← List.take_add]
    · have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_congr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r) _ _
        (hout.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self _ (((hn.filter _).drop).take.isChain)).symm)
      exact hp.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.collapse_consumption_pair _ (hn.filter _) r c s hb hc hg hbs)

/-- 概要：消費証跡に正の末尾保持選択を接続すると通常の一行を得る（BF §1.5.8）。
方針：先行部を集約し、最後の正の選択によって max を消費長と選択長の和へ戻す。
規約：先行部は空でもよい。最後の共有文字を残す終状態を厳密に保持する。
使われ方：水平零歩成分を含む内側区間を実際の元の TR 一行へ復元する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix.close {row removed out middle : List α}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix row removed out middle) (hn : row.Nodup) (s : ℕ)
    (hs : 0 < s) (hb : s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle row).length) :
    ∃ r : ℕ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row, r)] removed
      [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (out ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle row).take s)]
      (middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle row).take (s - 1)) := by
  obtain ⟨r, c, hr, hc, hg, hm, ho⟩ := h.normalize hn
  have hav : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle row = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).drop c := by
    rw [hm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn]
  have hbs : s ≤ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).drop c).length := by rw [← hav]; exact hb
  have htotal : c + s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by
    simp only [List.length_drop] at hbs
    omega
  have hword : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (out ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle row).take s) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (c + s) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_left_append out _, ho, hav]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.collapse_consumption_pair _ (hn.filter _) r c s hr hc hg hbs).trans
      (congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take t)
        (Nat.max_eq_right (show r ≤ c + s by omega)))
  have hstate : middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle row).take (s - 1) =
      removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (c + s - 1) := by
    rw [hav, hm, List.append_assoc, ← List.take_add]
    congr 2
    omega
  refine ⟨c + s, ?_⟩
  rw [hword, hstate]
  exact .cons (by omega) htotal (.nil _)

/-- 概要：消費証跡の後の通常の一行を、先行部と同じ終状態で融合する（BF §1.5.8）。
方針：最後の通常の一行から正の選択長と終状態を取り出し、close を適用する。
規約：先行消費が選択零の段だけでもよい。
使われ方：次が垂直移動である水平区間の全体を一行へ戻す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix.close_of_prefix {row removed out middle last finish : List α}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix row removed out middle) (hn : row.Nodup) (s : ℕ)
    (hfinal : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row, s)] middle [last] finish) :
    ∃ r : ℕ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row, r)] removed [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (out ++ last)] finish := by
  cases hfinal with
  | cons hs hb ht =>
    cases ht
    exact h.close hn s hs hb

/-- 概要：非空出力を持つ同じ行の消費証跡は通常の一行の成功を与える（BF §1.5.8）。
方針：集約選択の正値性を非空性から得て、最後の除外を通常の末尾保持に戻す。
規約：元の終状態は指定せず、通常の一行の実際の抽出成功を返す。
使われ方：最後の水平区間は最終行の内側射影が空でもまとめて閉じられる。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix.reduction {row removed out finish : List α}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix row removed out finish) (hn : row.Nodup) (hne : out ≠ []) :
    ∃ r : ℕ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [(row, r)] removed = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out) := by
  obtain ⟨r, _, hb, _, _, _, ho⟩ := h.normalize hn
  have hr : 0 < r := by
    by_contra hh
    have he : r = 0 := by omega
    rw [he, List.take_zero] at ho
    exact hne ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_nil_iff _).mp ho)
  refine ⟨r, ?_⟩
  rw [ho]
  simpa only [List.append_nil] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row r [] removed [] hr hb rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
