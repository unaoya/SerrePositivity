module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputOccurrences

/-!
模型。文献の定義との比較は後で
# 切断の出力頂点と左右リストの所属

概要：Berger–Fresse §2.2.1 の出力頂点を切断点を含む take・drop の所属で表す。
方針：左右の出現位置とリスト位置を有限添字の値で比較する。
規約：全射性や切断の非零性を要求しない。
使われ方：部分合成による全出力族の一致を代入リストの所属へ帰着する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：出力の零頂点の所属は左リストの色の所属と同値（BF §2.2.1）。
方針：切断点以下の出現位置を take の有限位置へ移す。
規約：切断点の文字を左リストに含める。
使われ方：合成の左リストの代入公式で零頂点を照合する。 -/
lemma zero_mem_edgeOutputVertices_iff_mem_take {n l : ℕ} (u : Fin l → Fin n)
    (p : Fin l) (k : Fin n) :
    0 ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p k ↔ k ∈ (List.ofFn u).take (p.val + 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zero_mem_edgeOutputVertices_iff]
  constructor
  · rintro ⟨i, hi, hu⟩
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val, ?_, ?_⟩
    · simp only [List.length_ofFn]
      have := i.isLt
      omega
    · simpa only [List.getElem_ofFn] using hu
  · intro hm
    obtain ⟨i, hi, hu⟩ := List.mem_take_iff_getElem.mp hm
    have hil : i < l := by simp only [List.length_ofFn] at hi; omega
    refine ⟨⟨i, hil⟩, ?_, ?_⟩
    · change i ≤ p.val
      omega
    · simpa only [List.getElem_ofFn] using hu

/-- 概要：出力の一頂点の所属は右リストの色の所属と同値（BF §2.2.1）。
方針：切断点以後の出現位置と drop 内の相対位置を対応させる。
規約：切断点の文字を右リストに含める。
使われ方：合成の右リストの代入公式で一頂点を照合する。 -/
lemma one_mem_edgeOutputVertices_iff_mem_drop {n l : ℕ} (u : Fin l → Fin n)
    (p : Fin l) (k : Fin n) :
    1 ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p k ↔ k ∈ (List.ofFn u).drop p.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.one_mem_edgeOutputVertices_iff]
  constructor
  · rintro ⟨i, hi, hu⟩
    have hli : p.val + (i.val - p.val) = i.val := by omega
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val - p.val, ?_, ?_⟩
    · simp only [List.length_drop, List.length_ofFn]
      have := i.isLt
      omega
    · simpa only [List.getElem_drop, List.getElem_ofFn, hli] using hu
  · intro hm
    obtain ⟨i, hi, hu⟩ := List.mem_iff_getElem.mp hm
    have hil : p.val + i < l := by
      simp only [List.length_drop, List.length_ofFn] at hi
      omega
    refine ⟨⟨p.val + i, hil⟩, ?_, ?_⟩
    · change p.val ≤ p.val + i
      omega
    · simpa only [List.getElem_drop, List.getElem_ofFn] using hu

/-- 概要：左右の色の所属が一致すれば出力頂点集合は一致（BF §2.2.1）。
方針：二頂点それぞれの所属を左右リストの所属へ戻す。
規約：比較する語の arity・長さ・切断点は異なってよい。
使われ方：残り・挿入ラベルの出力比較の共通界面。 -/
lemma edgeOutputVertices_eq_of_list_membership {n m l t : ℕ}
    (u : Fin l → Fin n) (v : Fin t → Fin m) (p : Fin l) (q : Fin t)
    (a : Fin n) (b : Fin m)
    (hL : a ∈ (List.ofFn u).take (p.val + 1) ↔ b ∈ (List.ofFn v).take (q.val + 1))
    (hR : a ∈ (List.ofFn u).drop p.val ↔ b ∈ (List.ofFn v).drop q.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices v q b := by
  apply Finset.ext
  intro s
  fin_cases s
  · change (0 : Fin 2) ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p a ↔ 0 ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices v q b
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zero_mem_edgeOutputVertices_iff_mem_take] using hL
  · change (1 : Fin 2) ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u p a ↔ 1 ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices v q b
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.one_mem_edgeOutputVertices_iff_mem_drop] using hR

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
