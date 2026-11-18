module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotInversionCounts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotCompositionSigns

/-!
模型。文献の定義との比較は後で
# 二出現色への内側辺作用の一般係数一致

概要：Berger–Fresse §2.2.6・§3.1 の二出現色分岐で合成係数と二段作用の係数を比較する。
方針：両向き交差逆転と最初の指定出現の削除順位を合わせ、元の合成指数を加える。
規約：正の内側 arity と任意の内外語次数。
使われ方：部分合成則の一般符号等式の最後の分岐。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

local notation "r₀" => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k (Fin.mk 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k))

/-- 概要：二出現色の内側辺分岐で合成係数と二段作用の係数が一致（BF §2.2.6・§3.1）。
方針：一活動位置の列置換による逆転差に合成指数を加え、偶数差を除く。
規約：内外語次数は任意、指定色は外側切断点色と異なる。
使われ方：二段切断和の一般係数等式を全分岐で閉じる。 -/
lemma compositionCoefficient_nonpivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k a.partition *
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition =
        a.actionCoefficient := by
  have Hq := a.property.2
  rw [ha] at Hq
  have hc := a.inversionCount_nonpivot hn q ha hp
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase_pair u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) r₀
    (a.nonpivot_first_mem_active q ha hp)
  have hpos := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_caesura a.property.1 r₀ (a.nonpivot_first_caesura q ha hp)
  have hcol : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) r₀ =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1) k := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k⟩]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_prefix_degree u a.val.1 a.property.1 k).symm
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase_balance u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn a.property.1) r₀ (a.nonpivot_first_mem_active q ha hp)
  rw [hpos, hcol] at hb
  have hrank : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val r₀ ≤ d := by
    have hcard : (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card = d := by
      simpa only [Fintype.card_subtype] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.card_caesuras_basisWord u
    calc
      _ ≤ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card := by
        apply Finset.card_le_card
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩
      _ = d := hcard
  have hcZ := congrArg (fun z : ℕ => (z : ℤ)) hc
  have hoZ := congrArg (fun z : ℕ => (z : ℤ)) ho
  have hbZ := congrArg (fun z : ℕ => (z : ℤ)) hb
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hcZ hoZ hbZ
  have hg : ((∑ r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r r₀ + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r₀ r) : ℕ) : ℤ) +
        2 * (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) r₀ : ℤ) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val r₀ : ℤ) +
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1) k : ℤ) := by omega
  have hm := congrArg (fun z : ℤ => (e : ℤ) * z) hg
  have heq : ((e * (d - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val r₀) +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition) :
          ℕ) : ℤ).negOnePow =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) +
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) + d * e +
          e * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1) k : ℕ) : ℤ).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨-(e : ℤ) * (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) r₀ : ℤ), ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hrank]
    nlinarith
  have hs := congrArg (fun z : ℤˣ => (z : ℤ)) heq
  simp only [Int.coe_negOnePow_natCast] at hs
  rw [a.compositionSign_nonpivot q ha hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount (a.compositePosition_nondegenerate hn)]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.actionCoefficient, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv, Equiv.coe_fn_mk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut.coefficient, ha]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount a.property.1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount Hq.2,
    ← pow_add, hs]
  simp only [pow_add]
  ring

/-- 概要：二出現色分岐の実際の合成切断項は二段作用の係数付き出力（BF §2.2.6）。
方針：全出力族の一致と一般係数等式を連結する。
規約：任意の可換環と正の内側 arity。
使われ方：実際の左右辺の有限和の二出現色分岐を項ごとに同定する。 -/
lemma compositionEdgeCutTerm_nonpivot (A : Type*) [CommRing A] (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (hn : 0 < n) (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositionEdgeCutTerm A u v k a.partition hn a.compositePosition =
      a.actionCoefficient • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
        a.outputFamily_tupleDegree_all := by
  rw [a.compositionEdgeCutTerm_outputFamily A hn, a.compositionCoefficient_nonpivot hn q ha hp]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
