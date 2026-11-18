module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowEndOffsets

/-!
模型。文献の定義との比較は後で
# Schedule の部分和で指定した削除係数

概要：Berger–Fresse §1.4.4 の行末の符号を行長の座標だけで表す。
方針：同じ抽出証明書に行末位置と区切りの順位の二つの公式を適用する。
規約：出力の全射性・非退化性は要求しない。
使われ方：一文字行を削除する微分項を頂点境界の交代符号と照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定された行末の削除係数は行番号の交代符号（BF §1.4.4）。
方針：部分和による行末位置を実際の区切り列の評価に代入する。
規約：k は出力の有限添字、i は非最終行の番号。
使われ方：退化出力も含む微分の項に具体的な位置と符号を与える。 -/
lemma deletionCoefficient_schedule_rowEnd {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (i : Fin d) (k : Fin out.length)
    (hk : (((List.ofFn (fun j => (r.val j).val)).take (i.val + 1)).sum - 1) = k.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
      (-1 : ℤ) ^ i.val := by
  obtain ⟨picked, he, hn, hl, hlengths, hp⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEnds_of_reduction w r out h
  have hib : i.val + 1 < picked.length := by rw [hl]; omega
  have hget := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_getElem? picked hn i.val hib
  rw [List.map_take, hlengths, hk] at hget
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_raw_rowEnd _ picked hn _ i.val k hget
  simpa only [List.ofFn_getElem] using hp

/-- 概要：非最終の一文字行を削除する係数は頂点境界の符号（BF §1.4.4）。
方針：一文字行の末尾位置はその行より前の行長の総和に等しい。
規約：i.castSucc で最後以外の頂点を指定する。
使われ方：一文字行の削除による頂点境界項の符号を一致させる。 -/
lemma deletionCoefficient_singleton_nonfinal {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (i : Fin (d + 1)) (hi : (r.val i.castSucc).val = 1) (k : Fin out.length)
    (hk : ((List.ofFn (fun j => (r.val j).val)).take i.val).sum = k.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k =
      (-1 : ℤ) ^ i.val := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_schedule_rowEnd w r out h i k
  have hib : i.val < (List.ofFn (fun j => (r.val j).val)).length := by
    simp only [List.length_ofFn]
    omega
  rw [List.take_succ_eq_append_getElem hib, List.sum_append]
  have he : (List.ofFn (fun j => (r.val j).val))[i.val] = 1 := by
    rw [List.getElem_ofFn]
    have hidx : (⟨i.val, by omega⟩ : Fin (d + 2)) = i.castSucc := Fin.ext rfl
    exact (congrArg (fun j => (r.val j).val) hidx).trans hi
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, he, Nat.add_sub_cancel, hk]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
