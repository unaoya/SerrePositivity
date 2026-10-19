module

public import SerrePositivity.EInfinity.TableReduction.RowFusionCollapse
public import SerrePositivity.EInfinity.TableReduction.SharedBoundaryChain

/-!
# 後続の非退化性を保つ同じ二行の融合

概要：Berger–Fresse §1.5.8 の外側表圧縮で、非退化な後続へ先行行を融合する。
方針：同じ行の次の抽出は前行末から始まり、共有文字一つの連結は非退化となる。
規約：元の二行連結語自体は共有文字を重複してよい。
使われ方：表全体の圧縮出力の非退化性を後ろから帰納的に構成する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：非退化な後続の先頭と同じ行を融合しても非退化（BF §1.5.8）。
方針：共有境界と同じ終状態の融合成功を明示し、共有末尾の連結規則を適用する。
規約：先行行は非重複、正で有効な行長。後続は次の除外状態から実際に成功する。
使われ方：重複行圧縮の成功・縮約不変性・非退化性を同時に得る。 -/
lemma rowFusion_isChain_of_tail (removed row : List α) (hn : row.Nodup) (r s : ℕ)
    (hr : 0 < r) (hb : r ≤ (available removed row).length)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : reduceRows ((row, s) :: rest)
      (removed ++ (available removed row).take (r - 1)) = some tail)
    (hc : tail.IsChain (· ≠ ·)) :
    ∃ out', reduceRows ((row, r + s - 1) :: rest) removed = some out' ∧
      collapse out' = collapse ((available removed row).take r ++ tail) ∧
      out'.IsChain (· ≠ ·) := by
  obtain ⟨hs, hbs, after, ha, ho⟩ := reduceRows_cons_success _ _ _ _ _ ht
  have hf := rowFusion_success removed row hn r s hr hb hs hbs rest after ha
  have hf' : reduceRows ((row, r + s - 1) :: rest) removed =
      some (((available removed row).take r).dropLast ++ tail) := by
    rw [ho]
    exact hf
  refine ⟨_, hf', ?_, ?_⟩
  all_goals
    have hi : r - 1 < (available removed row).length := by omega
    let a := (available removed row)[r - 1]
    have hlast : ((available removed row).take r).getLast? = some a := by
      rw [List.getLast?_take, ite_eq_right (show r ≠ 0 by omega),
        List.getElem?_eq_getElem hi, Option.some_or]
    have hhead : tail.head? = some a := by
      rw [ho, available_after_take removed row hn, List.drop_eq_getElem_cons hi]
      cases s with
      | zero => omega
      | succ s => simp only [List.take_succ_cons, List.cons_append, List.head?_cons]; rfl
  · exact collapse_dropLast_append_shared _ _ a hlast hhead
  · exact isChain_dropLast_append_shared _ _ a hlast hhead
      (List.Pairwise.isChain ((hn.filter _).take)) hc

end SerrePositivity.EInfinity.TableReduction
