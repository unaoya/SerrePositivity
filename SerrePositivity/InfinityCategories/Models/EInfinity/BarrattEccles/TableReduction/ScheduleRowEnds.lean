module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOffsets

/-!
模型。文献の定義との比較は後で
# Schedule の非最終行末と行順序

概要：Berger–Fresse §1.4.4 の受け取り行を行末の位置から指定する。
方針：行末は次の行の開始位置−1 であり、現在行の開始位置以上であることを使う。
規約：非最終行は Fin d で数える。
使われ方：削除位置より前の区切りが削除行より前の行に属することを示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：非最終行の末尾の出力位置（BF §1.4.4）。
方針：次の行の開始位置から 1 を引く。
規約：零始まりの自然数位置。
使われ方：直前の出現が属する行末を Schedule 上で表す。 -/
def scheduleEnd {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d) : ℕ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.succ - 1

/-- 概要：行末の位置は先行行長の部分和−1（BF §1.4.4）。
方針：次の行の添字の自然数値を評価する。
規約：全ての非最終行に適用する。
使われ方：既存の行末のリストの公式に接続する。 -/
lemma scheduleEnd_eq_prefix {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i =
      ((List.ofFn (fun j => (r.val j).val)).take (i.val + 1)).sum - 1 := rfl

/-- 概要：行末の位置は同じ行の開始位置以上（BF §1.4.4）。
方針：次の部分和が現在の部分和に正の行長を足したものであることを使う。
規約：行長の正値性は Schedule の条件から得る。
使われ方：位置の順序から受け取り行と削除行の順序を反映する。 -/
lemma scheduleOffset_le_end {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i.castSucc ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i := by
  have hib : i.val < (List.ofFn (fun j => (r.val j).val)).length := by
    simp only [List.length_ofFn]
    omega
  have hp := r.property.1 i.castSucc
  have he : (List.ofFn (fun j => (r.val j).val))[i.val] = (r.val i.castSucc).val := by
    rw [List.getElem_ofFn]
    exact congrArg (fun j => (r.val j).val) (Fin.ext rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_eq_prefix, List.take_succ_eq_append_getElem hib, List.sum_append, he]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  change ((List.ofFn (fun j => (r.val j).val)).take i.val).sum ≤ _
  omega

/-- 概要：行末が指定行の開始位置より前なら行番号も前（BF §1.4.4）。
方針：反対の行順序なら開始位置の単調性と行末の下界に矛盾する。
規約：指定する削除行には最終行も許す。
使われ方：二つの行が異なることと先行関係を同時に与える。 -/
lemma row_lt_of_end_lt_start {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin d)
    (j : Fin (d + 1)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j) : i.castSucc < j := by
  by_contra hn
  have hj : j ≤ i.castSucc := le_of_not_gt hn
  have hs := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_strictMono r).monotone hj
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_le_end r i
  omega

/-- 概要：成功 table の非最終行末の列は Schedule の行末位置を列挙する（BF §1.4.4）。
方針：抽出行の長さの証明書を部分和の公式へ代入する。
規約：出力の退化を仮定しない。
使われ方：区切りの位置から受け取り行を特定する。 -/
lemma rowEnds_eq_scheduleEnds {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (picked : List (List (Fin n))) (hn : ∀ row ∈ picked, row ≠ [])
    (hl : picked.length = d + 1)
    (he : picked.map List.length = List.ofFn (fun j => (r.val j).val)) (i : Fin d) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions picked)[i.val]? = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i) := by
  have hi : i.val + 1 < picked.length := by rw [hl]; omega
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowEndPositions_getElem? picked hn i.val hi, List.map_take, he]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
