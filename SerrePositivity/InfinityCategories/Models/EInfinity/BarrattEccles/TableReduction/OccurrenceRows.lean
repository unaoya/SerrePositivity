module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows

/-!
模型。文献の定義との比較は後で
# 削除位置の抽出行と前の同値の出現

概要：Berger–Fresse §1.4.4 の行長の移動で使う削除位置の所属行を特定する。
方針：平坦化した位置を行と内部位置へ分け、行の重複のなさを使う。
規約：全射性・非退化性を仮定しない。
使われ方：最終出現を削除する行より前に受け取り行があることを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：平坦化した語の各位置は一つの行の内部位置に属する（BF §1.4.4）。
方針：先頭行の長さとの比較で再帰する。
規約：空の行があっても存在の主張は成立する。
使われ方：削除位置を実際の抽出行とその行内の位置に分ける。 -/
lemma flatten_position_decomposition {α : Type*} (picked : List (List α))
    (k : ℕ) (hk : k < picked.flatten.length) :
    ∃ before row after, picked = before ++ row :: after ∧
      ∃ j : Fin row.length, k = before.flatten.length + j.val := by
  induction picked generalizing k with
  | nil => simp only [List.flatten_nil, List.length_nil] at hk; omega
  | cons row rest ih =>
    by_cases hb : k < row.length
    · exact ⟨[], row, rest, rfl, ⟨k, hb⟩, by simp⟩
    · have ht : k - row.length < rest.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hk
        omega
      obtain ⟨before, current, after, he, j, hj⟩ := ih (k - row.length) ht
      refine ⟨row :: before, current, after, ?_, j, ?_⟩
      · simp only [he, List.cons_append]
      · simp only [List.flatten_cons, List.length_append]
        omega

/-- 概要：重複のない行の同じ値の前の出現はその行より前にある（BF §1.4.4）。
方針：前の位置が同じ行なら、要素の単射性から同じ位置となり矛盾する。
規約：位置は自然数で指定し、全体の語を先行・現在行・後続に分ける。
使われ方：削除行と受け取り行が異なり、受け取り行が先行することを導く。 -/
lemma previous_position_lt_row_start {α : Type*} (pre row post : List α)
    (hn : row.Nodup) (i j : ℕ) (hi : i < row.length) (hj : j < pre.length + i)
    (he : (pre ++ (row ++ post))[j]'(by simp only [List.length_append]; omega) = row[i]) :
    j < pre.length := by
  by_contra hb
  have hge : pre.length ≤ j := by omega
  have hrow : j - pre.length < row.length := by omega
  rw [List.getElem_append_right hge, List.getElem_append_left hrow] at he
  have hidx : (⟨j - pre.length, hrow⟩ : Fin row.length) = ⟨i, hi⟩ :=
    (List.nodup_iff_injective_get.mp hn) he
  have hval := congrArg Fin.val hidx
  change j - pre.length = i at hval
  omega

/-- 概要：行の分離条件は任意の後続部分でも成立する（BF §1.4.4）。
方針：先行行で帰納し、再帰条件の後続部分を取る。
規約：行内部の排除と行の重複のなさをともに保持する。
使われ方：削除行と受け取り行の間の不変条件を取り出す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows.append_right {α : Type*} (before rest : List (List α))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows (before ++ rest)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows rest := by
  induction before with
  | nil => exact h
  | cons row before ih => exact ih h.2.2

/-- 概要：分離した行の指定行は重複を持たない（BF §1.4.4）。
方針：先行行を取り除いて現在行の条件を得る。
規約：空の行にも成立する。
使われ方：実際の削除位置の前の同値の出現を先行行へ移す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows.row_nodup {α : Type*} (before : List (List α))
    (row : List α) (after : List (List α))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows (before ++ row :: after)) : row.Nodup :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows.append_right before (row :: after) h).1

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
