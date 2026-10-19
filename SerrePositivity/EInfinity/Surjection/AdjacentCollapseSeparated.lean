module

public import SerrePositivity.EInfinity.Surjection.AdjacentCollapseEndpoints
public import SerrePositivity.EInfinity.Surjection.AdjacentCollapseConcatenation

/-!
# 異なる端点を持つ語の連続重複縮約

概要：Berger–Fresse §1.5.8 の内側成分間で、異なる端点の境界を保って縮約を接続する。
方針：縮約語は常に非退化で、先頭・末尾保存によって連結も非退化になる。
規約：各語の内部には任意の隣接重複を許す。空語の境界条件は空虚。
使われ方：垂直移動の前後で復元内側語を実際の全内側語へ接続する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：任意の語の連続重複縮約は隣接非一致（BF §1.5.8）。
方針：先頭付加の一致分岐ではコピーを省き、不一致分岐では非退化な先頭を付ける。
規約：元の語の非退化性は要求しない。
使われ方：合成出力から復元する内側語の非退化性。 -/
lemma collapse_isChain (xs : List α) : (collapse xs).IsChain (· ≠ ·) := by
  induction xs with
  | nil => simp only [collapse, List.isChain_nil]
  | cons a xs ih =>
    rw [collapse]
    cases he : collapse xs with
    | nil => simp only [prepend, List.isChain_singleton]
    | cons b tail =>
      rw [he] at ih
      by_cases hab : a = b
      · simpa only [prepend, ite_eq_left hab] using ih
      · simpa only [prepend, ite_eq_right hab] using List.isChain_cons_cons.mpr ⟨hab, ih⟩

/-- 概要：異なる末尾・先頭の境界では縮約は連結と交換する（BF §1.5.8）。
方針：両縮約語の非退化性と端点保存から連結を非退化にし、二重縮約を消す。
規約：境界条件は Option 所属で指定し、空語も含む。
使われ方：水平区間ごとの内側復元を全出力の内側復元へ同定する。 -/
lemma collapse_append_of_separated (pre post : List α)
    (hb : ∀ a ∈ pre.getLast?, ∀ b ∈ post.head?, a ≠ b) :
    collapse (pre ++ post) = collapse pre ++ collapse post := by
  have hc := (collapse_isChain pre).append (collapse_isChain post) (by
    simpa only [collapse_getLast?, collapse_head?] using hb)
  calc
    _ = collapse (collapse pre ++ collapse post) := by
      rw [collapse_left_append]
      exact collapse_append_congr pre _ _
        (collapse_eq_self _ (collapse_isChain post)).symm
    _ = _ := collapse_eq_self _ hc

end SerrePositivity.EInfinity.Surjection.AdjacentCollapse
