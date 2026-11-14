module

public import SerrePositivity.KST.DerivedBlowup.UniversalSplitCoordinates
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation

/-!
概要：KST Def3.1・Lemma3.6 の普遍チャート関係族の有限弱正則性。
方針：変数再配置で負の独立モニック一次関係族へ移し、既存の一般補題を使う。
規約：可換環の弱正則列として証明し、新しい正則性仮定を置かない。
使われ方：普遍チャート Koszul 複体の解消性。
-/

@[expose] public noncomputable section

universe v

namespace SerrePositivity.KST.DerivedBlowup

open SerrePositivity.BhattScholze.Andre

variable {I : Type v} [DecidableEq I]

/-- 概要：普遍チャートの再配置関係式は負のモニック一次関係式。
方針：一次多項式の評価を展開する。
規約：KST Def3.1。使われ方：独立モニック族の正則性の適用。 -/
theorem universalSplitEquiv_relation (i : I) (j : ChartIndex i) :
    universalSplitEquiv i (universalRelation i j) =
      -monicRelation
        (Polynomial.X - Polynomial.C (radialCoordinate i * MvPolynomial.X (some j))) j := by
  change universalSplitMap i (universalRelation i j) = _
  rw [universalSplitMap_relation]
  simp [monicRelation, neg_sub]

/-- 概要：異なる有限個の普遍チャート関係式は弱正則列。
方針：再配置同型で負のモニック関係族へ移し、その弱正則性を戻す。
規約：KST Def3.1・Lemma3.6。使われ方：有限チャートの Koszul 解消。 -/
theorem universalRelation_fin_isWeaklyRegular (i : I) {n : ℕ}
    (s : Fin n → ChartIndex i) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (ChartRing (UniversalBase I) i)
      (List.ofFn fun k => universalRelation i (s k)) := by
  let rs := List.ofFn fun k => universalRelation i (s k)
  let e := universalSplitEquiv i
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, e, List.map_ofFn, Function.comp_def, universalSplitEquiv_relation] using
      monicRelation_neg_fin_isWeaklyRegular
        (fun j : ChartIndex i => Polynomial.X -
          Polynomial.C (radialCoordinate i * MvPolynomial.X (some j)))
        (fun j => Polynomial.monic_X_sub_C _) s hs

/-- 概要：異なる有限個の普遍関係式の Koszul 複体は関係式商を解消する。
方針：証明した弱正則性を既存の有限 Koszul 解消定理へ渡す。
規約：KST Lemma3.6。使われ方：普遍チャートから任意基底への導来底変更。 -/
theorem universalRelation_fin_isKoszulResolution (i : I) {n : ℕ}
    (s : Fin n → ChartIndex i) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun k => universalRelation i (s k)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (universalRelation_fin_isWeaklyRegular i s hs)

end SerrePositivity.KST.DerivedBlowup
