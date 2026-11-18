module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapPrefix

/-!
模型。文献の定義との比較は後で
# 同じ行へ射影される抽出区間の消費証跡

概要：Berger–Fresse §1.5.8 の水平区間を、空選択と全除外を許して内側へ射影する。
方針：射影した選択と除外の二つの長さを記録し、可用行の部分単射射影を使う。
規約：全ての元の行の射影は一つの行。選択末尾が残ることは要求しない。
使われ方：垂直成分間の水平区間を元の内側一行へ融合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：射影選択長と射影除外長の差は零または一（BF §1.5.8）。
方針：元の選択を末尾以外と末尾一文字に分け、filterMap の長さを比較する。
規約：元の選択は正で可用行長以下。射影選択は空でもよい。
使われ方：内側射影を全消費または末尾保持の証跡として記録する。 -/
lemma filterMap_consumption_bounds (f : α → Option β) (xs : List α) (r : ℕ)
    (hr : 0 < r) (hb : r ≤ xs.length) :
    ((xs.take (r - 1)).filterMap f).length ≤ ((xs.take r).filterMap f).length ∧
      ((xs.take r).filterMap f).length ≤ ((xs.take (r - 1)).filterMap f).length + 1 := by
  have hi : r - 1 < xs.length := by omega
  have he : xs.take r = xs.take (r - 1) ++ [xs[r - 1]] := by
    have he := List.take_append_getElem hi
    have ha : r - 1 + 1 = r := by omega
    simpa only [ha] using he.symm
  rw [he, List.filterMap_append, List.length_append]
  cases hf : f xs[r - 1] <;> simp [List.filterMap, hf]

variable [DecidableEq α] [DecidableEq β]

/-- 概要：一つの行に射影される任意の抽出区間はその行の消費証跡を持つ（BF §1.5.8）。
方針：先行抽出で帰納し、射影の選択長・除外長と可用行を一致させる。
規約：末尾を捨てる行や内側文字のない行も含み、終状態は実際の射影に等しい。
使われ方：同じ内側置換の水平区間の全体を元の内側行で抽出する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.filterMap_consumption {rows : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rows removed picked finish) (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a') (source : List β)
    (hrows : ∀ p ∈ rows, p.1.filterMap f = source) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix source (removed.filterMap f) (picked.flatten.filterMap f)
      (finish.filterMap f) := by
  induction h with
  | nil => simpa only [List.flatten_nil, List.filterMap_nil] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix.nil _
  | @cons row r rest removed picked finish hr hb ht ih =>
    have hrow := hrows (row, r) List.mem_cons_self
    have hi := ih (fun p hp => hrows p (List.mem_cons_of_mem _ hp))
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row
    let s := ((xs.take r).filterMap f).length
    let c := ((xs.take (r - 1)).filterMap f).length
    have hbounds := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_consumption_bounds f xs r hr hb
    have hav : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) source = xs.filterMap f := by
      rw [← hrow, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_filterMap f hf]
    have hpick : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) source).take s =
        (xs.take r).filterMap f := by
      rw [hav, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
    have hstate : (removed ++ xs.take (r - 1)).filterMap f =
        removed.filterMap f ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) source).take c := by
      rw [List.filterMap_append, hav, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
    have hs : s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) source).length := by
      have hh := congrArg List.length hpick
      simp only [List.length_take] at hh
      change _ = s at hh
      omega
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix source ((removed ++ xs.take (r - 1)).filterMap f)
      (picked.flatten.filterMap f) (finish.filterMap f) at hi
    rw [hstate] at hi
    have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix.cons s c hs hbounds.1 hbounds.2 hi
    simpa only [List.flatten_cons, List.filterMap_append, hpick] using hh

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
