module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapFinal
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace

/-!
模型。文献の定義との比較は後で
# 最終行の末尾を除いて保持する全抽出の射影

概要：Berger–Fresse §1.5.7–9 の nullary 比較に必要な全抽出の部分射影を証明する。
方針：非最終行では末尾保持の状態公式、最終行では非空選択の先頭部分公式を使う。
規約：射影選択は全行で非空。最終行の元の末尾だけは捨ててもよい。
使われ方：指定値が一出現の元の成功表から空語合成表の成功を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：全選択が非空で、非最終行の末尾が残る条件（BF §1.5.7）。
方針：選択行の順に再帰して必要な保持条件を記録する。
規約：最終行の末尾は射影で捨ててもよい。
使われ方：部分単射による全抽出の射影の入力。 -/
def FilterMapReady (f : α → Option β) : List (List α) → Prop
  | [] => True
  | word :: rest => word.filterMap f ≠ [] ∧
      (rest ≠ [] → ∃ a b, word.getLast? = some a ∧ f a = some b) ∧
      FilterMapReady f rest

variable [DecidableEq α] [DecidableEq β]

/-- 概要：末尾保持条件を満たす全成功表は部分単射で射影できる（BF §1.5.7–9）。
方針：証跡で帰納し、後続がある行では除外状態を保ち、最後では先頭部分を抽出する。
規約：元の選択長は射影した選択語の長さへ変える。
使われ方：nullary の順方向の成功 Schedule を構成する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.filterMap_reduceRows {rows : List (List α × ℕ)}
    {removed : List α} {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked)
    (f : α → Option β) (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapReady f picked) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows f rows picked) (removed.filterMap f) =
      some (picked.flatten.filterMap f) := by
  induction h with
  | nil => rfl
  | @cons row r rest removed picked hr hb ht ih =>
    have hnonempty := he.1
    have hav := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_filterMap f hf removed row
    have hpick : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take
        (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length =
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f := by
      rw [hav, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
    have hpositive : 0 < (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length :=
      List.length_pos_iff.mpr hnonempty
    have hbound : (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length ≤
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).length := by
      have hl := congrArg List.length hpick
      simp only [List.length_take] at hl
      omega
    by_cases hn : picked = []
    · subst picked
      have hrest : rest = [] := List.length_eq_zero_iff.mp (by
        simpa only [List.length_nil] using ht.length.symm)
      subst rest
      have hcondition : 0 < (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length ∧
          (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length ≤
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).length := ⟨hpositive, hbound⟩
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows, List.zipWith_cons_cons, List.zipWith_nil_left,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows, hcondition, and_true, ite_true, Option.map_some, List.append_nil,
        List.flatten_cons, List.flatten_nil, hpick]
    · obtain ⟨_, _, hu⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_selection_retained_last f
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row) r hr hb (he.2.1 hn)
      have hstate : (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)).filterMap f =
          removed.filterMap f ++
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take
              ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length - 1) := by
        rw [List.filterMap_append, hav, hu]
      have htail := ih he.2.2
      rw [hstate] at htail
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success (row.filterMap f)
        (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f).length (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows f rest picked)
        (removed.filterMap f) (picked.flatten.filterMap f) hpositive hbound htail
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows, List.zipWith_cons_cons, List.flatten_cons,
        List.filterMap_append, hpick] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
