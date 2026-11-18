module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapAvailable

/-!
模型。文献の定義との比較は後で
# 既に除外された文字の削除と全抽出

概要：Berger–Fresse §1.5.7 の nullary 比較で、削除する文字を先に除外した表を扱う。
方針：可用行の全文字は射影に残るので、長さ・先頭部分・除外更新を保って再帰する。
規約：部分単射の none となる全ての文字を初期除外状態に含める。
使われ方：削除後の成功表を指定値を初めから除外した元の表へ比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：全ての文字が射影に残るリストは長さを保つ（BF §1.5.7）。
方針：各先頭の some 値を取り出して帰納する。
規約：リスト外の文字に条件を課さない。
使われ方：指定値を既に除外した可用行の長さを比較する。 -/
lemma filterMap_length_of_retained (f : α → Option β) (xs : List α)
    (h : ∀ a ∈ xs, ∃ b, f a = some b) : (xs.filterMap f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := h a (by simp)
    simp only [List.filterMap_cons, hb, List.length_cons]
    exact congrArg Nat.succ (ih (fun a ha => h a (by simp [ha])))

/-- 概要：全ての文字が残る場合は先頭部分の長さも変わらない（BF §1.5.7）。
方針：リストと先頭部分の長さで帰納する。
規約：take の長さは元のリスト長を超えてもよい。
使われ方：全抽出の選択語と次の除外状態を同時に比較する。 -/
lemma filterMap_take_of_retained (f : α → Option β) (xs : List α)
    (h : ∀ a ∈ xs, ∃ b, f a = some b) (r : ℕ) :
    (xs.take r).filterMap f = (xs.filterMap f).take r := by
  induction xs generalizing r with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := h a (by simp)
    cases r with
    | zero => simp
    | succ r =>
      simp only [List.take_succ_cons, List.filterMap_cons, hb]
      exact congrArg (b :: ·) (ih (fun a ha => h a (by simp [ha])) r)

variable [DecidableEq α] [DecidableEq β]

/-- 概要：既に除外された文字の部分単射による削除は全抽出と可換（BF §1.5.7）。
方針：各可用行が全て射影に残ることから、選択と状態更新を再帰的に照合する。
規約：失敗する表も含め、初期除外には none となる全ての文字を含む。
使われ方：nullary 合成表と指定値を早期に除外した元の表の全体の比較。 -/
lemma reduceRows_filterMap_of_discarded_mem (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (rows : List (List α × ℕ)) (removed : List α)
    (hd : ∀ a, f a = none → a ∈ removed) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (rows.map (fun p => (p.1.filterMap f, p.2))) (removed.filterMap f) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed).map (List.filterMap f) := by
  induction rows generalizing removed with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨row, r⟩
    have hret : ∀ a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row, ∃ b, f a = some b := by
      intro a ha
      have hn : a ∉ removed := (List.mem_filter.mp ha).2 |> of_decide_eq_true
      cases he : f a with
      | none => exact False.elim (hn (hd a he))
      | some b => exact ⟨b, rfl⟩
    have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_length_of_retained f _ hret
    have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_of_retained f _ hret
    simp only [List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_filterMap f hf, hl]
    split
    · rw [← ht (r - 1), ← List.filterMap_append, ih]
      · simp only [Option.map_map, Function.comp_def, List.filterMap_append, ht]
      · intro a ha
        exact List.mem_append_left _ (hd a ha)
    · rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
