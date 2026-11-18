module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 元の先行抽出の除外状態の単調性

概要：Berger–Fresse §1.5.7 の最終除外前の水平成分で指定値が途中でも残ることを示す。
方針：元の除外リストが各行の更新で含まれ続けることを証跡で帰納する。
規約：リストの順序や重複数ではなく所属を比較する。
使われ方：終状態で未除外の指定値が各選択行の末尾以外に現れないことを導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

variable {α : Type*} [DecidableEq α]

/-- 概要：元の始状態で除外された文字は終状態でも除外される（BF §1.5.7）。
方針：各行で除外リストを連結することを証跡で帰納する。
規約：任意の先行証跡に適用する。
使われ方：水平成分の全途中状態で指定値の未除外を保つ。 -/
lemma mem_finish_of_mem {rs : List (List α × ℕ)} {initial finish : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rs initial picked finish)
    (a : α) (ha : a ∈ initial) : a ∈ finish := by
  induction h with
  | nil => exact ha
  | cons hr hb ht ih => exact ih (List.mem_append_left _ ha)

/-- 概要：終状態で未除外の文字は始状態でも未除外（BF §1.5.7）。
方針：始状態から終状態への所属保存の対偶を使う。
規約：同じ先行証跡の任意の始状態について成立する。
使われ方：外側指定値の最終除外前の各行の条件を得る。 -/
lemma not_mem_initial {rs : List (List α × ℕ)} {initial finish : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix rs initial picked finish)
    (a : α) (ha : a ∉ finish) : a ∉ initial := fun hm => ha (h.mem_finish_of_mem a hm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
