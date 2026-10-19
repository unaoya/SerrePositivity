module

public import SerrePositivity.EInfinity.IntervalCuts.NonpivotInversionCounts
public import SerrePositivity.EInfinity.IntervalCuts.PivotCompositionSigns

/-!
# 二出現色への内側辺作用の一般係数一致

概要：Berger–Fresse §2.2.6・§3.1 の二出現色分岐で合成係数と二段作用の係数を比較する。
方針：両向き交差逆転と最初の指定出現の削除順位を合わせ、元の合成指数を加える。
規約：正の内側 arity と任意の内外語次数。
使われ方：部分合成則の一般符号等式の最後の分岐。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut

open Surjection

variable {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e} {k : Fin (m + 1)}

local notation "r₀" => occurrenceAt u.val k (Fin.mk 0 (occurrenceCount_pos u k))

/-- 概要：二出現色の内側辺分岐で合成係数と二段作用の係数が一致（BF §2.2.6・§3.1）。
方針：一活動位置の列置換による逆転差に合成指数を加え、偶数差を除く。
規約：内外語次数は任意、指定色は外側切断点色と異なる。
使われ方：二段切断和の一般係数等式を全分岐で閉じる。 -/
lemma compositionCoefficient_nonpivot (a : NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    compositionSign u v k a.partition *
      edgeSign (compositeBasisWord u v k a.partition hn).val a.compositePosition =
        a.actionCoefficient := by
  have Hq := a.property.2
  rw [ha] at Hq
  have hc := a.inversionCount_nonpivot hn q ha hp
  have ho := positionInversionCount_erase_pair u.val (activePositions u.val a.val.1) r₀
    (a.nonpivot_first_mem_active q ha hp)
  have hpos := positionRank_active_caesura a.property.1 r₀ (a.nonpivot_first_caesura q ha hp)
  have hcol : colorRank u.val (activePositions u.val a.val.1) r₀ =
      prefixDegree (m + 1) (edgeOutput u a.val.1) k := by
    unfold colorRank
    rw [occurrenceAt_value u.val k ⟨0, occurrenceCount_pos u k⟩]
    exact (edgeOutput_prefix_degree u a.val.1 a.property.1 k).symm
  have hb := positionInversionCount_erase_balance u.val (activePositions u.val a.val.1)
    (activePositions_injOn a.property.1) r₀ (a.nonpivot_first_mem_active q ha hp)
  rw [hpos, hcol] at hb
  have hrank : caesuraRank u.val r₀ ≤ d := by
    have hcard : (Finset.univ.filter (Caesura u.val)).card = d := by
      simpa only [Fintype.card_subtype] using card_caesuras_basisWord u
    calc
      _ ≤ (Finset.univ.filter (Caesura u.val)).card := by
        apply Finset.card_le_card
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩
      _ = d := hcard
  have hcZ := congrArg (fun z : ℕ => (z : ℤ)) hc
  have hoZ := congrArg (fun z : ℕ => (z : ℤ)) ho
  have hbZ := congrArg (fun z : ℕ => (z : ℤ)) hb
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hcZ hoZ hbZ
  have hg : ((∑ r ∈ (activePositions u.val a.val.1).erase r₀,
      (positionInversionTerm u.val r r₀ + positionInversionTerm u.val r₀ r) : ℕ) : ℤ) +
        2 * (lowerRank u.val (activePositions u.val a.val.1) r₀ : ℤ) =
      (caesuraRank u.val r₀ : ℤ) +
        (prefixDegree (m + 1) (edgeOutput u a.val.1) k : ℤ) := by omega
  have hm := congrArg (fun z : ℤ => (e : ℤ) * z) hg
  have heq : ((e * (d - caesuraRank u.val r₀) +
      positionInversionCount (compositeBasisWord u v k a.partition hn).val
        (activePositions (compositeBasisWord u v k a.partition hn).val a.compositePosition) :
          ℕ) : ℤ).negOnePow =
      ((positionInversionCount u.val (activePositions u.val a.val.1) +
        positionInversionCount v.val (activePositions v.val q) + d * e +
          e * prefixDegree (m + 1) (edgeOutput u a.val.1) k : ℕ) : ℤ).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨-(e : ℤ) * (lowerRank u.val (activePositions u.val a.val.1) r₀ : ℤ), ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hrank]
    nlinarith
  have hs := congrArg (fun z : ℤˣ => (z : ℤ)) heq
  simp only [Int.coe_negOnePow_natCast] at hs
  rw [a.compositionSign_nonpivot q ha hp,
    edgeSign_eq_inversionCount (a.compositePosition_nondegenerate hn)]
  simp only [actionCoefficient, faceCutEquiv, Equiv.coe_fn_mk, FaceCut.coefficient, ha]
  rw [edgeSign_eq_inversionCount a.property.1, edgeSign_eq_inversionCount Hq.2,
    ← pow_add, hs]
  simp only [pow_add]
  ring

/-- 概要：二出現色分岐の実際の合成切断項は二段作用の係数付き出力（BF §2.2.6）。
方針：全出力族の一致と一般係数等式を連結する。
規約：任意の可換環と正の内側 arity。
使われ方：実際の左右辺の有限和の二出現色分岐を項ごとに同定する。 -/
lemma compositionEdgeCutTerm_nonpivot (A : Type*) [CommRing A] (a : NestedEdgeCut u v k)
    (hn : 0 < n) (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    compositionEdgeCutTerm A u v k a.partition hn a.compositePosition =
      a.actionCoefficient • tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
        a.outputFamily_tupleDegree_all := by
  rw [a.compositionEdgeCutTerm_outputFamily A hn, a.compositionCoefficient_nonpivot hn q ha hp]

end SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut
