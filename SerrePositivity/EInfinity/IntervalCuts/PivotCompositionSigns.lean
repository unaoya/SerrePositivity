module

public import SerrePositivity.EInfinity.IntervalCuts.PivotInversionCounts
public import SerrePositivity.EInfinity.IntervalCuts.PivotBoundarySigns
public import SerrePositivity.EInfinity.IntervalCuts.NestedCompositionSigns
public import SerrePositivity.EInfinity.IntervalCuts.IteratedNestedSum

/-!
# 切断点色への内側辺作用の一般係数一致

概要：Berger–Fresse §2.2.6・§3.1 の切断点色分岐で合成係数と二段作用の係数を比較する。
方針：合成逆転数の二ブロック公式と切断点削除の順位釣り合いを整数の偶奇で比較する。
規約：正の内側 arity と任意の内外語次数。
使われ方：部分合成則の二段切断和の切断点色分岐。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut

open Surjection

variable {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e} {k : Fin (m + 1)}

/-- 概要：切断点色への挿入の切断符号は二段作用の二交換符号付きの内外切断符号（BF §3.1）。
方針：合成逆転数の交差項を切断点削除の位置順位・色順位へ変え、偶数差を除く。
規約：内外語次数は任意である。
使われ方：実際の余代入の交換符号と合成切断符号の一般の一致。 -/
lemma edgeSign_pivot (a : NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) :
    edgeSign (compositeBasisWord u v k a.partition hn).val a.compositePosition =
      (-1 : ℤ) ^ (d * e + e * prefixDegree (m + 1) (edgeOutput u a.val.1) k) *
        edgeSign u.val a.val.1 * edgeSign v.val q := by
  have Hq := a.property.2
  rw [ha] at Hq
  have hc := a.inversionCount_pivot hn hp q ha
  have ho := positionInversionCount_last u.val (activePositions u.val a.val.1) a.val.1
    (Finset.mem_insert_self _ _) (fun j hj => activePosition_le_pivot a.property.1 hj)
  rw [hp] at ho
  have hpos : positionRank (activePositions u.val a.val.1) a.val.1 = d := by
    rw [positionRank_active_pivot a.property.1]
    simpa only [Fintype.card_subtype] using card_caesuras_basisWord u
  have hcol : colorRank u.val (activePositions u.val a.val.1) a.val.1 =
      prefixDegree (m + 1) (edgeOutput u a.val.1) k := by
    unfold colorRank
    rw [hp]
    exact (edgeOutput_prefix_degree u a.val.1 a.property.1 k).symm
  have hb := positionInversionCount_erase_balance u.val (activePositions u.val a.val.1)
    (activePositions_injOn a.property.1) a.val.1 (Finset.mem_insert_self _ _)
  rw [hpos, hcol] at hb
  have hcZ := congrArg (fun z : ℕ => (z : ℤ)) hc
  have hoZ := congrArg (fun z : ℕ => (z : ℤ)) ho
  have hbZ := congrArg (fun z : ℕ => (z : ℤ)) hb
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hcZ hoZ hbZ
  have hg : ((((activePositions u.val a.val.1).erase a.val.1).filter
      (fun r => k < u.val r)).card : ℤ) +
        2 * (lowerRank u.val (activePositions u.val a.val.1) a.val.1 : ℤ) =
      (d : ℤ) + (prefixDegree (m + 1) (edgeOutput u a.val.1) k : ℤ) := by omega
  have hm := congrArg (fun z : ℤ => (e : ℤ) * z) hg
  have heq : (positionInversionCount
      (compositeBasisWord u v k a.partition hn).val
      (activePositions (compositeBasisWord u v k a.partition hn).val a.compositePosition) :
        ℤ).negOnePow =
      ((positionInversionCount u.val (activePositions u.val a.val.1) +
        positionInversionCount v.val (activePositions v.val q) + d * e +
          e * prefixDegree (m + 1) (edgeOutput u a.val.1) k : ℕ) : ℤ).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨-(e : ℤ) * (lowerRank u.val (activePositions u.val a.val.1) a.val.1 : ℤ), ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hs := congrArg (fun z : ℤˣ => (z : ℤ)) heq
  simp only [Int.coe_negOnePow_natCast] at hs
  rw [edgeSign_eq_inversionCount (a.compositePosition_nondegenerate hn),
    edgeSign_eq_inversionCount a.property.1, edgeSign_eq_inversionCount Hq.2, hs]
  simp only [pow_add]
  ring

/-- 概要：切断点色の内側辺分岐で合成係数と二段作用の係数が一致（BF §2.2.6・§3.1）。
方針：この分岐の合成符号一と合成切断符号の二交換公式を合わせる。
規約：内側切断点の符号を実際の面切断係数へ同定する。
使われ方：部分合成則の切断点色分岐の係数等式を閉じる。 -/
lemma compositionCoefficient_pivot (a : NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) :
    compositionSign u v k a.partition *
      edgeSign (compositeBasisWord u v k a.partition hn).val a.compositePosition =
        a.actionCoefficient := by
  rw [a.compositionSign_pivot hp, one_mul, a.edgeSign_pivot hn q ha hp]
  simp only [actionCoefficient, faceCutEquiv, Equiv.coe_fn_mk, FaceCut.coefficient, ha]

/-- 概要：切断点色分岐の実際の合成切断項は二段作用の係数付き出力（BF §2.2.6）。
方針：全出力族の一致に一般の係数等式を代入する。
規約：任意の可換環と正の内側 arity。
使われ方：実際の左右辺の有限和の切断点色分岐を項ごとに同定する。 -/
lemma compositionEdgeCutTerm_pivot (A : Type*) [CommRing A] (a : NestedEdgeCut u v k)
    (hn : 0 < n) (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 = k) :
    compositionEdgeCutTerm A u v k a.partition hn a.compositePosition =
      a.actionCoefficient • tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
        a.outputFamily_tupleDegree_all := by
  rw [a.compositionEdgeCutTerm_outputFamily A hn, a.compositionCoefficient_pivot hn q ha hp]

end SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut
