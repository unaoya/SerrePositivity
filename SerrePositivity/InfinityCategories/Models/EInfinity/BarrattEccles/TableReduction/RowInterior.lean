module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ResidualRowEnds

/-!
模型。文献の定義との比較は後で
# 長い行の内部位置と一文字行の分離

概要：Berger–Fresse §1.4.4 の残余削除集合を行内の任意の位置で判定する。
方針：異なる二行の部分和が重ならないことを利用する。
規約：最終行の内部位置も含む。
使われ方：逆構成の挿入点が長い延長行に属すれば残余集合へ戻せる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：前の行の終了境界は後の行の開始位置以下（BF §1.4.4）。
方針：一成分を足した部分和と長い部分和を比較する。
規約：前後の行は任意の異なる行。
使われ方：行内区間どうしの非交差を検証する。 -/
lemma scheduleOffset_add_length_le {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i j : Fin (d + 1)) (hij : i < j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + (r.val i).val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j := by
  have hi : i.val < (List.ofFn (fun k => (r.val k).val)).length := by
    simpa only [List.length_ofFn] using i.isLt
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_take_mono (List.ofFn (fun k => (r.val k).val))
    (by change i.val < j.val at hij; omega : i.val + 1 ≤ j.val)
  rw [List.take_succ_eq_append_getElem hi, List.sum_append] at hs
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.getElem_ofFn] at hs
  exact hs

/-- 概要：同じ位置を含む二つの行の番号は一致（BF §1.4.4）。
方針：異なる行番号なら前の終了境界が後の開始位置以下となり矛盾する。
規約：位置は自然数でよい。
使われ方：逆構成した挿入点の順方向の削除行を一意に決める。 -/
lemma row_unique_of_bounds {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i j : Fin (d + 1)) (k : ℕ)
    (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i ≤ k) (hi' : k < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + (r.val i).val)
    (hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j ≤ k) (hj' : k < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j + (r.val j).val) : i = j := by
  rcases lt_trichotomy i j with hij | he | hji
  · have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_add_length_le r i j hij
    omega
  · exact he
  · have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_add_length_le r j i hji
    omega

/-- 概要：非最終行の末尾位置は行番号を一意に決める（BF §1.4.4）。
方針：異なる行の行内範囲が交わらないことを行末へ適用する。
規約：行長は Schedule の正値性を使う。
使われ方：直前出現の行末位置から順方向の受け取り行を同定する。 -/
lemma scheduleEnd_injective {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r) := by
  intro i j he
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r i
  have hj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r j
  have hloi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_le_end r i
  have hloj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_le_end r j
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.row_unique_of_bounds r i.castSucc j.castSucc (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r i)
    hloi (by omega) (by omega) (by omega)
  exact Fin.ext (congrArg (fun k : Fin (d + 1) => k.val) hf)

/-- 概要：長さ 2 以上の行の全ての位置は一文字行の削除位置でない（BF §1.4.4）。
方針：一致候補の行番号を前・同じ・後に分け、行区間の非交差を使う。
規約：出力の値は使わず長さと行内範囲だけを使う。
使われ方：逆構成の最終出現削除が残余集合に入ることを保証する。 -/
lemma position_in_long_row_not_singleton {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i : Fin (d + 1)) (hi : 1 < (r.val i).val) (out : List (Fin n))
    (hl : out.length = n + d) (k : Fin out.length)
    (hlo : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i ≤ k.val)
    (hhi : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + (r.val i).val) :
    k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out hl := by
  intro hx
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hx
  have hval : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r j = k.val := congrArg Fin.val he
  have hjlen : (r.val j).val = 1 := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy j i with hji | rfl | hij
  · have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_add_length_le r j i hji
    omega
  · omega
  · have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_add_length_le r i j hij
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
