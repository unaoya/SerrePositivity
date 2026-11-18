module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseBudget
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleasedDonorStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TerminalDonorStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntermediatePrefix

/-!
模型。文献の定義との比較は後で
# 最初の変更行を延長した逆向きの抽出

概要：Berger–Fresse §1.4.4 の解放値の探索から変更後の後続抽出を実際に構成する。
方針：停止行を解放値で分割し、通常と最終末尾を分け、先行抽出を連結する。
規約：変更後の抽出成功や削除後出力の一致を追加仮定しない。
使われ方：行末側から最終出現側へ戻る逆の削除対を作る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：探索の停止条件を満たす行を一文字延ばすと元の出力に解放値だけを挿入（BF §1.4.4）。
方針：解放値の位置で利用可能語を分け、二種類の逆の局所抽出を使う。
規約：元の行長は正、元の行は重複を持たない。
使われ方：探索の停止行で変更後の抽出を構成する。 -/
lemma released_chosen_extraction {α : Type*} [DecidableEq α]
    (removed row : List α) (a : α) (r : ℕ) (rest : List (List α × ℕ)) (out : List α)
    (hn : row.Nodup) (hr : 0 < r)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: rest) (removed ++ [a]) = some out)
    (hc : a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ∨
      (rest = [] ∧ a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ∧
        a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r + 1))) :
    ∃ pre post, out = pre ++ post ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r + 1) :: rest) removed = some (pre ++ a :: post) := by
  have havail : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).Nodup := hn.filter _
  rcases hc with hhit | ⟨rfl, hnot, hlast⟩
  · obtain ⟨j, hj, hv⟩ := List.mem_take_iff_getElem.mp hhit
    have hjlen : j < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := (Nat.lt_min.mp hj).2
    have hjr : j < r := (Nat.lt_min.mp hj).1
    obtain ⟨pre, post, he, hp, hpre, hpost⟩ :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nodup_split_at (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row) havail ⟨j, hjlen⟩
    rw [hv] at he hpre hpost
    let s := r - pre.length
    have hs : 0 < s := by dsimp only [s]; change pre.length = j at hp; omega
    have hlength : r = pre.length + s := by dsimp only [s]; omega
    obtain ⟨_, hb, tail, ht, hout⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    have hpostbound : s ≤ post.length := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_donor_split removed row pre post a he hpre hpost, List.length_append] at hb
      omega
    have htail : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
        ((removed ++ [a]) ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s - 1)) =
          some tail := by rw [← hlength]; exact ht
    have hnew := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_released_donor_step removed row pre post a s hs hpostbound he
      hpre hpost rest tail htail
    refine ⟨pre, post.take s ++ tail, ?_, ?_⟩
    · rw [hout, hlength, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_selected_split removed row pre post a s he hpre hpost).1,
        List.append_assoc]
    · have hlen : r + 1 = pre.length + (s + 1) := by omega
      rw [hlen]
      simpa only [List.append_assoc, List.cons_append] using hnew
  · obtain ⟨j, hj, hv⟩ := List.mem_take_iff_getElem.mp hlast
    have hjlen : j < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := (Nat.lt_min.mp hj).2
    have hjr : j < r + 1 := (Nat.lt_min.mp hj).1
    have hjge : r ≤ j := by
      by_contra hb
      apply hnot
      exact List.mem_take_iff_getElem.mpr ⟨j, by omega, hv⟩
    have hjeq : j = r := by omega
    obtain ⟨pre, post, he, hp, hpre, hpost⟩ :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nodup_split_at (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row) havail ⟨j, hjlen⟩
    rw [hv] at he hpre hpost
    have hprelen : pre.length = r := by change pre.length = j at hp; omega
    obtain ⟨hold, hnew⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_terminal_donor_step removed row pre post a
      (by omega) he hpre hpost
    have hsource : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [(row, pre.length)] (removed ++ [a]) = some out := by
      rw [hprelen]; exact h
    have hout : out = pre := Option.some.inj (hsource.symm.trans hnew)
    refine ⟨pre, [], by simpa only [List.append_nil] using hout, ?_⟩
    rw [← hprelen]
    exact hold

/-- 概要：探索した停止行を延長すると後続出力には解放値一文字だけが加わる（BF §1.4.4）。
方針：停止行の局所抽出を解放状態の先行証跡へ連結し、元の抽出と比較する。
規約：元の後続列の成功だけを使う。
使われ方：行末側から戻した後続の成功抽出と削除後出力一致を与える。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch.extend_extraction {n : ℕ} {a : Fin n}
    {rs before after : List (List (Fin n) × ℕ)}
    {removed finish : List (Fin n)} {picked : List (List (Fin n))}
    {chosen : List (Fin n) × ℕ}
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after)
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows rs) (out suffix : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rs (removed ++ [a]) = some out)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (chosen :: after) (finish ++ [a]) = some suffix) :
    ∃ pre post, out = pre ++ post ∧ a ∉ pre ∧ a ∉ post ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (chosen.1, chosen.2 + 1) :: after) removed =
        some (pre ++ a :: post) := by
  have hmem : chosen ∈ rs := by rw [hs.decomposition]; simp
  have hchosen := hc chosen hmem
  obtain ⟨pre, post, hold, hnew⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.released_chosen_extraction finish chosen.1 a chosen.2
    after suffix hchosen.1 hchosen.2.2.2 ht hs.selection_cases
  have hprefix := hs.toPrefix
  have horiginal := hprefix.append_early_exclusion a hs.not_mem_selected (chosen :: after)
    suffix ht
  have hsource : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rs (removed ++ [a]) = some (picked.flatten ++ suffix) := by
    rw [hs.decomposition]
    exact horiginal
  have hout : out = picked.flatten ++ suffix := Option.some.inj (h.symm.trans hsource)
  have hout' : out = (picked.flatten ++ pre) ++ post := by
    rw [hout, hold, List.append_assoc]
  have habsent : a ∉ out := by
    intro hm
    have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.not_mem_removed_of_mem_output rs (removed ++ [a]) out h a hm
    exact hn (by simp)
  refine ⟨picked.flatten ++ pre, post, hout', ?_, ?_, ?_⟩
  · intro hm
    apply habsent
    rw [hout']
    exact List.mem_append_left _ hm
  · intro hm
    apply habsent
    rw [hout']
    exact List.mem_append_right _ hm
  · have hchanged := hprefix.append _ _ hnew
    simpa only [List.append_assoc] using hchanged

/-- 概要：成功した後続列と予算から一文字だけ増やした逆の抽出を構成（BF §1.4.4）。
方針：必ず停止する探索の証明書を取り、停止行を延長した抽出を構成する。
規約：変更行の存在や変更後の成功は追加仮定しない。
使われ方：行末削除の逆構成で延長する行と具体的な出力を同時に得る。 -/
lemma releaseSearch_constructs_extension {n : ℕ} (rs : List (List (Fin n) × ℕ))
    (removed : List (Fin n)) (a : Fin n) (out : List (Fin n))
    (hne : rs ≠ []) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows rs) (hn : removed.Nodup) (ha : a ∉ removed)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rs (removed ++ [a]) = some out)
    (hb : removed.length + 1 + (rs.map (fun p => p.2 - 1)).sum + 1 = n) :
    ∃ before picked finish chosen after pre post,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after ∧
      finish.Nodup ∧ a ∉ finish ∧ out = pre ++ post ∧ a ∉ pre ∧ a ∉ post ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (chosen.1, chosen.2 + 1) :: after) removed =
        some (pre ++ a :: post) := by
  obtain ⟨before, picked, finish, chosen, after, hs, hfn, hfa, suffix, ht⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.releaseSearch_exists rs removed a out hne hc hn ha h hb
  obtain ⟨pre, post, hout, hp, hpost, hnew⟩ := hs.extend_extraction hc out suffix h ht
  exact ⟨before, picked, finish, chosen, after, pre, post, hs, hfn, hfa, hout, hp, hpost, hnew⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
