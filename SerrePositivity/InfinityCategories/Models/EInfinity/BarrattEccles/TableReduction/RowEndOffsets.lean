module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RawRowEndSigns

/-!
模型。文献の定義との比較は後で
# 行長の部分和による table の削除位置

概要：Berger–Fresse §1.4.4 の非最終行末を行長の部分和で表示する。
方針：行のリストで帰納し、先頭行の長さによる位置の移動を計算する。
規約：位置は零始まり、全行は非空とする。
使われ方：一文字行の削除位置と Schedule の添字を対応させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：第 i 非最終行末は最初の i+1 行の総長−1（BF §1.4.4）。
方針：先頭行を除くと位置がその長さだけ移る。
規約：最後の行以外を自然数の添字で指定する。
使われ方：区切り位置を指定された行長だけから計算する。 -/
lemma rowEndPositions_getElem? {α : Type*} (picked : List (List α))
    (hn : ∀ row ∈ picked, row ≠ []) (i : ℕ) (hi : i + 1 < picked.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i]? =
      some (((picked.take (i + 1)).map List.length).sum - 1) := by
  induction picked generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons row rest ih =>
    have hp : 0 < row.length := List.length_pos_iff.mpr (hn row (by simp))
    have hrest : ∀ r ∈ rest, r ≠ [] := fun r hr => hn r (by simp [hr])
    cases rest with
    | nil => simp only [List.length_cons, List.length_nil] at hi; omega
    | cons next rest =>
      cases i with
      | zero => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions]
      | succ i =>
        have hb : i + 1 < (next :: rest).length := by
          simp only [List.length_cons] at hi ⊢
          omega
        have he := ih hrest i hb
        have ht : 0 < (((next :: rest).take (i + 1)).map List.length).sum := by
          have hnext : 0 < next.length := List.length_pos_iff.mpr (hrest next (by simp))
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
          omega
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions, List.getElem?_cons_succ, List.getElem?_map, he,
          Option.map_some, List.take_succ_cons, List.map_cons, List.sum_cons]
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at ht
        congr 1
        omega

/-- 概要：成功 table の第 i 区切りは Schedule の部分和−1（BF §1.4.4）。
方針：抽出された各行の長さの証明書を部分和の式へ代入する。
規約：退化した出力を含む全成功 table を扱う。
使われ方：削除位置と行番号の交代符号を同じ座標で表す。 -/
lemma rowEndOffsets_of_reduction {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ picked, picked.flatten = out ∧ picked.length = d + 1 ∧
      ∀ i : Fin d, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? =
        some (((List.ofFn (fun j => (r.val j).val)).take (i.val + 1)).sum - 1) := by
  obtain ⟨picked, he, hn, hl, hlengths, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_of_reduction w r out h
  refine ⟨picked, he, hl, ?_⟩
  intro i
  have hi : i.val + 1 < picked.length := by rw [hl]; omega
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_getElem? picked hn i.val hi, List.map_take, hlengths]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
