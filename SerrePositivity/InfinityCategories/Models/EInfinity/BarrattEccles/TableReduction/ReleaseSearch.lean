module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleasedState

/-!
模型。文献の定義との比較は後で
# 解放値で最初に影響を受ける行の探索

概要：Berger–Fresse §1.4.4 の行末削除の逆対応で最初に延長する後続行を特定する。
方針：解放値をまだ選ばない行を飛ばし、除外長の予算で最後の行の延長を保証する。
規約：通常は元の選択先頭 r 文字への出現、最後だけは r+1 文字への出現を許す。
使われ方：逆の行長移動で延長する行の存在を、元の成功抽出から得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：解放値が最初に選択へ入る行までの実際の先行抽出（BF §1.4.4）。
方針：行内部での出現、最後の延長での出現、未選択行の通過を区別する。
規約：先行部分の行リスト・選択行・終端状態を保持する。
使われ方：逆対応の最初の変更行を曖昧な選択なしに指定する。 -/
inductive ReleaseSearch {n : ℕ} (a : Fin n) :
    List (List (Fin n) × ℕ) → List (Fin n) → List (List (Fin n) × ℕ) →
      List (List (Fin n)) → List (Fin n) → (List (Fin n) × ℕ) →
        List (List (Fin n) × ℕ) → Prop
  | hit {row : List (Fin n)} {r : ℕ} {rest : List (List (Fin n) × ℕ)} {removed : List (Fin n)}
      (ha : a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r) :
      ReleaseSearch a ((row, r) :: rest) removed [] [] removed (row, r) rest
  | terminal {row : List (Fin n)} {r : ℕ} {removed : List (Fin n)}
      (hx : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r)
      (ha : a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + 1)) :
      ReleaseSearch a [(row, r)] removed [] [] removed (row, r) []
  | skip {row : List (Fin n)} {r : ℕ} {rest before after : List (List (Fin n) × ℕ)}
      {removed finish : List (Fin n)} {picked : List (List (Fin n))}
      {chosen : List (Fin n) × ℕ} (hr : 0 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
      (hx : a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r)
      (next : ReleaseSearch a rest (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1))
        before picked finish chosen after) :
      ReleaseSearch a ((row, r) :: rest) removed ((row, r) :: before)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r :: picked) finish chosen after

/-- 概要：除外予算の合う成功した後続列では逆探索が必ず変更行に到達（BF §1.4.4）。
方針：未選択行で予算と成功を保ち、最後では利用可能長が r+1 であることを使う。
規約：元の状態は解放値 a を除外し、探索する状態はその一文字を解放する。
使われ方：逆対応の延長行の存在と元の後続抽出を同時に確保する。 -/
lemma releaseSearch_exists {n : ℕ} (rs : List (List (Fin n) × ℕ)) (removed : List (Fin n))
    (a : Fin n) (out : List (Fin n)) :
    rs ≠ [] → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows rs → removed.Nodup → a ∉ removed →
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rs (removed ++ [a]) = some out →
      removed.length + 1 + (rs.map (fun p => p.2 - 1)).sum + 1 = n →
      ∃ before picked finish chosen after,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after ∧
        finish.Nodup ∧ a ∉ finish ∧
        ∃ suffix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (chosen :: after) (finish ++ [a]) = some suffix := by
  induction rs generalizing removed out with
  | nil => intro hne; exact False.elim (hne rfl)
  | cons p rest ih =>
    intro _ hrows hn ha hsuccess hbudget
    rcases p with ⟨row, r⟩
    obtain ⟨hrNodup, hrLen, hrAll, hrPos⟩ := hrows (row, r) (by simp)
    by_cases hx : a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r
    · exact ⟨[], [], removed, (row, r), rest, .hit hx, hn, ha, out, hsuccess⟩
    · cases rest with
      | nil =>
        have hcard := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_complete_length_add row removed hrNodup hrLen hrAll hn
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero] at hbudget
        have hlen : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length = r + 1 := by omega
        have hm : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row := by
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.mem_filter, decide_eq_true_eq]
          exact ⟨hrAll a, ha⟩
        have he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row :=
          List.take_of_length_le (by omega)
        have hlast : a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + 1) := he.symm ▸ hm
        exact ⟨[], [], removed, (row, r), [], .terminal hx hlast, hn, ha, out, hsuccess⟩
      | cons next rest =>
        obtain ⟨_, hb, tail, ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hsuccess
        have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.intermediate_selected_eq removed row a r hx
        have hfree : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by
          have hl := congrArg List.length he
          simp only [List.length_take, Nat.min_eq_left hb] at hl
          omega
        obtain ⟨hnewNodup, hnewAbsent, hnewLen, hstates⟩ :=
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.released_state_step removed row a r hn hrNodup ha hrPos hfree hx
        let current := removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)
        have htail : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (next :: rest) (current ++ [a]) = some tail := by
          have hcongr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed (next :: rest)
            ((removed ++ [a]) ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (r - 1))
            (current ++ [a]) hstates
          exact hcongr.symm.trans ht
        have hnext : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows (next :: rest) := by
          intro q hq
          exact hrows q (List.mem_cons_of_mem _ hq)
        have hnextBudget : current.length + 1 +
            ((next :: rest).map (fun p => p.2 - 1)).sum + 1 = n := by
          simp only [List.map_cons, List.sum_cons] at hbudget
          change (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)).length + 1 + _ + 1 = n
          simp only [List.map_cons, List.sum_cons]
          omega
        obtain ⟨before, picked, finish, chosen, after, hs, hfn, hfa, suffix, hsuffix⟩ :=
          ih current tail (by simp) hnext hnewNodup hnewAbsent htail hnextBudget
        exact ⟨(row, r) :: before, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r :: picked,
          finish, chosen, after, .skip hrPos hfree hx hs, hfn, hfa, suffix, hsuffix⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
