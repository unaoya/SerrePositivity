module

public import SerrePositivity.EInfinity.TableReduction.RowFusion
public import SerrePositivity.EInfinity.TableReduction.DegenerateRows
public import SerrePositivity.EInfinity.Surjection.AdjacentCollapse

/-!
# 同じ二行の融合は縮約出力を保つ

概要：Berger–Fresse §1.5.8 の外側復元表の重複行を融合しても縮約出力は変わらない。
方針：前行末と次行頭の共有文字の二コピーを明示し、一つを消す。
規約：元の行は非重複。元の抽出出力の非退化性は要求しない。
使われ方：垂直移動で繰り返された外側行を元の行数へ戻す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ隣接行の融合は成功と連続重複縮約した出力を保つ（BF §1.5.8）。
方針：二行の共有文字を同じ可用行の添字 r−1 で評価し、二コピーを縮める。
規約：後続 table と初期除外は任意。
使われ方：外側復元表の重複行の反復融合を正当化する。 -/
lemma rowFusion_collapse (removed row : List α) (hn : row.Nodup) (r s : ℕ)
    (rest : List (List α × ℕ)) (out : List α)
    (h : reduceRows ((row, r) :: (row, s) :: rest) removed = some out) :
    ∃ out', reduceRows ((row, r + s - 1) :: rest) removed = some out' ∧
      collapse out' = collapse out := by
  obtain ⟨hr, hb, middle, hm, _⟩ := reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, _, _, _, _⟩ := reduceRows_cons_success _ _ _ _ _ hm
  obtain ⟨tail, ho, hf⟩ := rowFusion_of_success removed row hn r s rest out h
  refine ⟨_, hf, ?_⟩
  rw [ho, available_after_take removed row hn]
  cases r with
  | zero => omega
  | succ r =>
    cases s with
    | zero => omega
    | succ s =>
      have hi : r < (available removed row).length := by omega
      simp only [Nat.add_sub_cancel]
      rw [← List.take_concat_get' _ r hi, List.drop_eq_getElem_cons hi]
      simp only [List.dropLast_concat, List.take_succ_cons, List.append_assoc,
        List.singleton_append]
      exact (collapse_duplicate_in_context _ _ _).symm

end SerrePositivity.EInfinity.TableReduction
