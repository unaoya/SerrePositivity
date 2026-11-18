module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusionCollapse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SharedBoundaryChain

/-!
模型。文献の定義との比較は後で
# 後続の非退化性を保つ同じ二行の融合

概要：Berger–Fresse §1.5.8 の外側表圧縮で、非退化な後続へ先行行を融合する。
方針：同じ行の次の抽出は前行末から始まり、共有文字一つの連結は非退化となる。
規約：元の二行連結語自体は共有文字を重複してよい。
使われ方：表全体の圧縮出力の非退化性を後ろから帰納的に構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：非退化な後続の先頭と同じ行を融合しても非退化（BF §1.5.8）。
方針：共有境界と同じ終状態の融合成功を明示し、共有末尾の連結規則を適用する。
規約：先行行は非重複、正で有効な行長。後続は次の除外状態から実際に成功する。
使われ方：重複行圧縮の成功・縮約不変性・非退化性を同時に得る。 -/
lemma rowFusion_isChain_of_tail (removed row : List α) (hn : row.Nodup) (r s : ℕ)
    (hr : 0 < r) (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, s) :: rest)
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (r - 1)) = some tail)
    (hc : tail.IsChain (· ≠ ·)) :
    ∃ out', _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r + s - 1) :: rest) removed = some out' ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out' = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r ++ tail) ∧
      out'.IsChain (· ≠ ·) := by
  obtain ⟨hs, hbs, after, ha, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_success removed row hn r s hr hb hs hbs rest after ha
  have hf' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r + s - 1) :: rest) removed =
      some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).dropLast ++ tail) := by
    rw [ho]
    exact hf
  refine ⟨_, hf', ?_, ?_⟩
  all_goals
    have hi : r - 1 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by omega
    let a := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row)[r - 1]
    have hlast : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take r).getLast? = some a := by
      rw [List.getLast?_take, ite_eq_right (show r ≠ 0 by omega),
        List.getElem?_eq_getElem hi, Option.some_or]
    have hhead : tail.head? = some a := by
      rw [ho, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take removed row hn, List.drop_eq_getElem_cons hi]
      cases s with
      | zero => omega
      | succ s => simp only [List.take_succ_cons, List.cons_append, List.head?_cons]; rfl
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.collapse_dropLast_append_shared _ _ a hlast hhead
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.isChain_dropLast_append_shared _ _ a hlast hhead
      (List.Pairwise.isChain ((hn.filter _).take)) hc

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
