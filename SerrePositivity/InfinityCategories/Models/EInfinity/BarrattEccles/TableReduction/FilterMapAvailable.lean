module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows

/-!
模型。文献の定義との比較は後で
# 部分的な単射による可用行の射影

概要：Berger–Fresse §1.5.8 の内側射影と既除外文字の処理を比較する。
方針：値を持つ部分で単射な filterMap は除外所属を保存する。
規約：射影が none となる外側文字は行と除外状態の両方から捨てる。
使われ方：任意の合成表の成功抽出を元の内側表の抽出へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α β : Type*}

/-- 概要：部分単射で定義された文字の除外所属は射影で保存される（BF §1.5.8）。
方針：filterMap の所属証人の値を単射性で元の文字に一致させる。
規約：none となる文字同士の単射性は要求しない。
使われ方：射影した行の除外判定を元の判定へ戻す。 -/
lemma mem_filterMap_of_partial_injective (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (removed : List α) (a : α) (b : β) (ha : f a = some b) :
    b ∈ removed.filterMap f ↔ a ∈ removed := by
  constructor
  · intro hb
    obtain ⟨a', hm, he⟩ := List.mem_filterMap.mp hb
    exact hf a' a b he ha ▸ hm
  · intro hm
    exact List.mem_filterMap.mpr ⟨a, hm, ha⟩

variable [DecidableEq α] [DecidableEq β]

/-- 概要：部分単射による行・除外状態の射影は可用行の射影と一致（BF §1.5.8）。
方針：行で帰納し、射影がある場合は除外所属の同値で分岐を照合する。
規約：元の行や除外リストの非重複性は要求しない。
使われ方：合成行の抽出の filterMap を元の内側行の抽出へ移す。 -/
lemma available_filterMap (f : α → Option β)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a')
    (removed row : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap f) (row.filterMap f) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).filterMap f := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    cases ha : f a with
    | none =>
      by_cases hr : a ∈ removed <;> simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, ha, hr] using ih
    | some b =>
      have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_filterMap_of_partial_injective f hf removed a b ha
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filterMap_cons, ha, List.filter_cons] at ih ⊢
      by_cases hr : a ∈ removed
      · have hb := hm.mpr hr
        simpa only [hr, hb, not_true_eq_false, decide_false, Bool.false_eq_true,
          ite_false] using ih
      · have hb := hm.not.mpr hr
        simpa only [hr, hb, not_false_eq_true, decide_true, ite_true,
          List.filterMap_cons, ha] using congrArg (b :: ·) ih

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
