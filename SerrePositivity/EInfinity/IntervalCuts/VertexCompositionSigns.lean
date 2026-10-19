module

public import SerrePositivity.EInfinity.IntervalCuts.RemainingActivePositions
public import SerrePositivity.EInfinity.IntervalCuts.InversionReindex
public import SerrePositivity.EInfinity.IntervalCuts.NestedCompositionSigns
public import SerrePositivity.EInfinity.IntervalCuts.IteratedNestedSum

/-!
# 頂点入力分岐の部分合成符号

概要：Berger–Fresse §2.2.6 の内側が頂点へ作用する分岐で一般の係数一致を証明する。
方針：残り活動位置と色の順序保存から逆転数と切断符号を保つ。
規約：正の内側 arity、外側語次数・置換語は任意。
使われ方：部分合成則の一般符号等式の頂点分岐。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut

open Surjection

variable {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e} {k : Fin (m + 1)}

/-- 概要：残り活動位置の一対は合成語で同じ逆転寄与を持つ（BF §2.2.4・§2.2.6）。
方針：位置の厳密順序と残り色の厳密順序をともに外側へ戻す。
規約：代入色の外側出力が非辺であることを仮定する。
使われ方：全活動集合の二重和で逆転数を比較する。 -/
lemma remainingPositionMap_inversionTerm (a : NestedEdgeCut u v k) (hn : 0 < n)
    (hk : edgeOutput u a.val.1 k ≠ edge) (q r : Fin (m + 1 + d))
    (hq : q ∈ activePositions u.val a.val.1) (hr : r ∈ activePositions u.val a.val.1) :
    positionInversionTerm (compositeBasisWord u v k a.partition hn).val
      (a.remainingPositionMap q) (a.remainingPositionMap r) =
        positionInversionTerm u.val q r := by
  have hqk := activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k hk q hq
  have hrk := activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k hk r hr
  have hvq : (compositeBasisWord u v k a.partition hn).val (a.remainingPositionMap q) =
      BarrattEccles.remainingPosition m n k ⟨u.val q, hqk⟩ := by
    rw [a.remainingPositionMap_of_ne q hqk, compositeBasisWord_outerPosition]
  have hvr : (compositeBasisWord u v k a.partition hn).val (a.remainingPositionMap r) =
      BarrattEccles.remainingPosition m n k ⟨u.val r, hrk⟩ := by
    rw [a.remainingPositionMap_of_ne r hrk, compositeBasisWord_outerPosition]
  simp only [positionInversionTerm, hvq, hvr, a.remainingPositionMap_lt_iff q r hqk hrk,
    remainingPosition_lt_iff]

/-- 概要：非辺出力への次数零代入は活動色の全逆転数を保つ（BF §2.2.4・§2.2.6）。
方針：全活動集合を外側集合の単射像へ同定し、二重和の各寄与を照合する。
規約：正の内側 arity、内側語次数零。
使われ方：頂点分岐の実際の切断符号の一致。 -/
lemma inversionCount_vertex (a : NestedEdgeCut u v k) (hn : 0 < n)
    (hk : edgeOutput u a.val.1 k ≠ edge) (he : e = 0) :
    positionInversionCount (compositeBasisWord u v k a.partition hn).val
      (activePositions (compositeBasisWord u v k a.partition hn).val a.compositePosition) =
        positionInversionCount u.val (activePositions u.val a.val.1) := by
  rw [← a.remainingPositionMap_image_of_degree_zero hn hk he]
  exact positionInversionCount_image_of_terms _ _ _ _ (a.remainingPositionMap_injOn hk)
    (fun q hq r hr => a.remainingPositionMap_inversionTerm hn hk q r hq hr)

/-- 概要：内側頂点分岐の合成切断符号は外側切断符号（BF §2.2.4・§2.2.6）。
方針：両辺の切断符号を活動色の逆転数へ戻し、その保存を使う。
規約：内側頂点入力は none として保持する。
使われ方：合成符号と実際の二段作用の符号の比較。 -/
lemma edgeSign_vertex (a : NestedEdgeCut u v k) (hn : 0 < n) (ha : a.val.2 = none) :
    edgeSign (compositeBasisWord u v k a.partition hn).val a.compositePosition =
      edgeSign u.val a.val.1 := by
  have H := a.property.2
  rw [ha] at H
  rw [edgeSign_eq_inversionCount (a.compositePosition_nondegenerate hn),
    edgeSign_eq_inversionCount a.property.1, a.inversionCount_vertex hn H.1 H.2]

/-- 概要：内側頂点分岐の実際の二段作用の係数は外側切断符号（BF §3.1）。
方針：内側次数零で二つの交換符号を消し、頂点入力の係数一を使う。
規約：内側 arity 零も含む。
使われ方：部分合成則の係数一致の右辺を簡約する。 -/
lemma actionCoefficient_vertex (a : NestedEdgeCut u v k) (ha : a.val.2 = none) :
    a.actionCoefficient = edgeSign u.val a.val.1 := by
  have H := a.property.2
  rw [ha] at H
  simp only [actionCoefficient, H.2, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, pow_zero,
    one_mul, faceCutEquiv, Equiv.coe_fn_mk, FaceCut.coefficient, ha, mul_one]

/-- 概要：内側頂点分岐では合成側の一般係数は二段作用の係数に一致（BF §2.2.6）。
方針：合成符号一・合成切断符号保存・二段作用の係数簡約を連結する。
規約：正の内側 arity、全外側語次数、全頂点分岐。
使われ方：部分合成則の二段切断和の頂点分岐を閉じる。 -/
lemma compositionCoefficient_vertex (a : NestedEdgeCut u v k) (hn : 0 < n)
    (ha : a.val.2 = none) :
    compositionSign u v k a.partition *
      edgeSign (compositeBasisWord u v k a.partition hn).val a.compositePosition =
        a.actionCoefficient := by
  rw [a.compositionSign_vertex ha, one_mul, a.edgeSign_vertex hn ha,
    a.actionCoefficient_vertex ha]

/-- 概要：頂点分岐の実際の合成切断項は二段作用の係数付き出力テンソル（BF §2.2.6）。
方針：全出力族の既存の一致と頂点分岐の一般係数等式を合わせる。
規約：任意の可換環、正の内側 arity。
使われ方：合成辺成分と二段作用の有限和の頂点分岐を項ごとに同定する。 -/
lemma compositionEdgeCutTerm_vertex (A : Type*) [CommRing A] (a : NestedEdgeCut u v k)
    (hn : 0 < n) (ha : a.val.2 = none) :
    compositionEdgeCutTerm A u v k a.partition hn a.compositePosition =
      a.actionCoefficient • tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
        a.outputFamily_tupleDegree_all := by
  rw [a.compositionEdgeCutTerm_outputFamily A hn, a.compositionCoefficient_vertex hn ha]

end SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut
