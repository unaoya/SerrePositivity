module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapPrefix

/-!
模型。文献の定義との比較は後で
# 射影した最終選択語の末尾を残す抽出

概要：Berger–Fresse §1.5.8 の垂直最終行で内側部分の末尾を共有端点として残す。
方針：射影した選択語の長さで一行を切り、射影後の末尾以外だけを除外する。
規約：元の選択末尾を射影が捨てる場合も許す。射影した選択語は非空とする。
使われ方：合成表の垂直成分の最終行を元の内側区間の最終行へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：捨てる末尾以外の元の除外を射影すると選択語全体が除外される（BF §1.5.8）。
方針：選択語を末尾以外と末尾の連結へ分け、末尾の none を消す。
規約：元の行長は行全体の長さ以下。末尾の射影は none。
使われ方：合成の実際の終状態と内側末尾を残した復元状態の差を計算する。 -/
lemma filterMap_selection_discarded_last (f : α → Option β) (xs : List α) (r : ℕ)
    (hb : r ≤ xs.length) (a : α) (ha : (xs.take r).getLast? = some a)
    (hf : f a = none) :
    (xs.take (r - 1)).filterMap f = (xs.take r).filterMap f := by
  have hl : (xs.take r).length = r := by
    rw [List.length_take, Nat.min_eq_left hb]
  have hs := List.take_append_getLast? (xs.take r)
  rw [hl, ha, Option.toList_some] at hs
  simp only [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] at hs
  have hp := congrArg (List.filterMap f) hs
  simpa only [List.filterMap_append, List.filterMap_cons, hf, List.filterMap_nil,
    List.append_nil] using hp

variable [DecidableEq α] [DecidableEq β]

/-- 概要：射影した非空選択語を末尾を残す実際の一行として抽出できる（BF §1.5.8）。
方針：先頭部分の射影の一致から行長条件と選択語を得て、除外状態を再構成する。
規約：終状態は元の終状態の射影ではなく、射影選択語の末尾を残した状態。
使われ方：外側文字で終わる合成最終行の内側末尾も共有端点として保持する。 -/
lemma filterMap_final_prefix (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (removed row : List α) (r : ℕ)
    (hn : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f ≠ []) :
    let picked := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row.filterMap f, picked.length)] (removed.filterMap f) [picked]
      (removed.filterMap f ++ picked.take (picked.length - 1)) := by
  let picked := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).filterMap f
  have hpick : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take picked.length =
      picked := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_filterMap f hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
  have hr : 0 < picked.length := List.length_pos_iff.mpr hn
  have hb : picked.length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).length := by
    have hl := congrArg List.length hpick
    simp only [List.length_take] at hl
    omega
  have hs : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take (picked.length - 1) =
      picked.take (picked.length - 1) := by
    have hh := congrArg (fun word : List β => word.take (picked.length - 1)) hpick
    simpa only [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] using hh
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(row.filterMap f, picked.length)] (removed.filterMap f)
      [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take picked.length]
      (removed.filterMap f ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f)).take (picked.length - 1)) :=
    .cons hr hb (.nil _)
  simpa only [hpick, hs] using ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
