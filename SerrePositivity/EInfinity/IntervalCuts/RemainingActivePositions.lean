module

public import SerrePositivity.EInfinity.IntervalCuts.RemainingPositionOrder
public import SerrePositivity.EInfinity.IntervalCuts.RemainingOutputs

/-!
# 外側活動位置の合成語への写像

概要：Berger–Fresse §2.2.6 の非辺出力への代入では外側活動位置を全て保持する。
方針：残り位置の順序保存と残り出力の辺条件から合成後の活動性を得る。
規約：集合全体の同定だけ内側語次数零を要求する。
使われ方：頂点分岐での切断符号の保存。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：非零切断の活動位置は辺出力色を持つ左側位置に一致（BF §2.2.3）。
方針：辺出力の活動位置を取り、左側単射性で指定位置へ同定する。
規約：切断点を含む。
使われ方：合成語で色と位置上限から活動性を復元する。 -/
lemma mem_activePositions_iff_output_and_le {n d : ℕ} (u : BasisWord n d)
    (p : Fin (n + d)) (h : EdgeNondegenerate u.val p) (q : Fin (n + d)) :
    q ∈ activePositions u.val p ↔ edgeOutput u p (u.val q) = edge ∧ q ≤ p := by
  constructor
  · intro hq
    exact ⟨(edgeOutput_eq_edge_iff u p h _).2 ⟨q, hq, rfl⟩,
      activePosition_le_pivot h hq⟩
  · rintro ⟨he, hq⟩
    obtain ⟨j, hj, hv⟩ := (edgeOutput_eq_edge_iff u p h _).1 he
    have heq := edge_left_injective h j q (activePosition_le_pivot h hj) hq hv
    rwa [heq] at hj

/-- 概要：非辺出力の色は活動位置の色に現れない（BF §2.2.3）。
方針：活動色なら辺出力を持つことに矛盾させる。
規約：指定色は任意。
使われ方：頂点分岐の全活動位置を残り位置として扱う。 -/
lemma activePosition_color_ne_of_nonedge {n d : ℕ} (u : BasisWord n d)
    (p : Fin (n + d)) (h : EdgeNondegenerate u.val p) (k : Fin n)
    (hk : edgeOutput u p k ≠ edge) (q : Fin (n + d)) (hq : q ∈ activePositions u.val p) :
    u.val q ≠ k := by
  intro he
  exact hk ((edgeOutput_eq_edge_iff u p h k).2 ⟨q, hq, he⟩)

namespace NestedEdgeCut

variable {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e} {k : Fin (m + 1)}

/-- 概要：外側残り位置を合成語へ送り、指定色では合成切断点を返す（BF §2.2.6）。
方針：残り位置の既存の埋め込みを全位置上の関数へ延ばす。
規約：指定色の値は活動集合への制限では使わない。
使われ方：外側活動集合の有限像を定義する。 -/
def remainingPositionMap (a : NestedEdgeCut u v k) (q : Fin (m + 1 + d)) :
    Fin (m + n + (d + e)) :=
  if hq : u.val q ≠ k then compositeOuterPosition u v k a.partition q hq
  else a.compositePosition

/-- 概要：残り位置上で延長写像は実際の合成位置（BF §2.2.6）。
方針：非指定色の分岐を評価する。
規約：証明項の違いを無視する。
使われ方：順序と文字の既存の公式を適用する。 -/
lemma remainingPositionMap_of_ne (a : NestedEdgeCut u v k) (q : Fin (m + 1 + d))
    (hq : u.val q ≠ k) :
    a.remainingPositionMap q = compositeOuterPosition u v k a.partition q hq := by
  simp only [remainingPositionMap, dite_eq_left hq]

/-- 概要：延長写像は残り位置間の厳密順序を保存し反映（BF §2.2.6）。
方針：実際の残り位置への等式を順序公式に代入する。
規約：指定色の二位置は含めない。
使われ方：活動集合上の単射性と逆転対の比較。 -/
lemma remainingPositionMap_lt_iff (a : NestedEdgeCut u v k)
    (q r : Fin (m + 1 + d)) (hq : u.val q ≠ k) (hr : u.val r ≠ k) :
    a.remainingPositionMap q < a.remainingPositionMap r ↔ q < r := by
  rw [a.remainingPositionMap_of_ne q hq, a.remainingPositionMap_of_ne r hr]
  exact compositeOuterPosition_lt_iff u v k a.partition q r hq hr

/-- 概要：非辺出力への代入では外側活動集合上の位置写像は単射（BF §2.2.6）。
方針：全活動色が残り色であり、その位置間の厳密順序を保存することを使う。
規約：内側語次数は任意。
使われ方：活動集合の像の個数と逆転数を保つ。 -/
lemma remainingPositionMap_injOn (a : NestedEdgeCut u v k)
    (hk : edgeOutput u a.val.1 k ≠ edge) :
    Set.InjOn a.remainingPositionMap (activePositions u.val a.val.1) := by
  intro q hq r hr he
  have hqk := activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k hk q hq
  have hrk := activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k hk r hr
  rcases lt_trichotomy q r with h | h | h
  · exact False.elim ((ne_of_lt ((a.remainingPositionMap_lt_iff q r hqk hrk).2 h)) he)
  · exact h
  · exact False.elim ((ne_of_lt ((a.remainingPositionMap_lt_iff r q hrk hqk).2 h)) he.symm)

/-- 概要：非辺出力への代入は外側の各活動位置を活動位置へ送る（BF §2.2.6）。
方針：切断点以下の位置順序と残り色の辺出力を保持する。
規約：正の内側 arity、内側語次数は任意。
使われ方：外側活動集合の像と合成活動集合の包含。 -/
lemma remainingPositionMap_mem_active (a : NestedEdgeCut u v k) (hn : 0 < n)
    (hk : edgeOutput u a.val.1 k ≠ edge) (q : Fin (m + 1 + d))
    (hq : q ∈ activePositions u.val a.val.1) :
    a.remainingPositionMap q ∈ activePositions
      (compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  have hqk := activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k hk q hq
  have hpk := activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k hk a.val.1
    (Finset.mem_insert_self _ _)
  apply (mem_activePositions_iff_output_and_le _ _ (a.compositePosition_nondegenerate hn) _).2
  constructor
  · rw [a.remainingPositionMap_of_ne q hqk, compositeBasisWord_outerPosition]
    rw [a.compositePosition_remaining_output hn]
    exact (edgeOutput_eq_edge_iff u a.val.1 a.property.1 _).2 ⟨q, hq, rfl⟩
  · rw [a.remainingPositionMap_of_ne q hqk, a.compositePosition_nonpivot_eq_outer hpk]
    rcases lt_or_eq_of_le (activePosition_le_pivot a.property.1 hq) with h | rfl
    · exact (compositeOuterPosition_lt u v k a.partition q a.val.1 hqk hpk h).le
    · exact le_rfl

/-- 概要：非辺出力への次数零代入は全活動集合を保存（BF §2.2.6）。
方針：活動集合の単射像の包含と両側の d+1 個という個数を合わせる。
規約：正の内側 arity と内側語次数零。
使われ方：頂点分岐での合成切断の全交換指数。 -/
lemma remainingPositionMap_image_of_degree_zero (a : NestedEdgeCut u v k) (hn : 0 < n)
    (hk : edgeOutput u a.val.1 k ≠ edge) (he : e = 0) :
    (activePositions u.val a.val.1).image a.remainingPositionMap =
      activePositions (compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact a.remainingPositionMap_mem_active hn hk q hq
  · rw [Finset.card_image_of_injOn (a.remainingPositionMap_injOn hk),
      activePositions_card _ _ (a.compositePosition_nondegenerate hn),
      activePositions_card u a.val.1 a.property.1, he]

end NestedEdgeCut

end SerrePositivity.EInfinity.IntervalCuts
