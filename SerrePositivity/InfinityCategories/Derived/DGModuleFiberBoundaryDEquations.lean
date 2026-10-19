module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryLegEquations

/-! # 候補データの N 側方程式

概要：非零の N 側成分 d を入れた左右の候補は、その未知集合の微分方程式を満たす。
方針：先頭置換による右辺の変化を対角射の合成と同定し、δd=t a+r_D を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残る検証を全体集合の三角形方程式に限定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：Left 側の先頭置換後の D 右辺は r_D+t a と異種等号で一致する。
方針：先頭置換による右辺の変化を共通の Hom 座標へ移す。
規約：HA Proposition 1.3.1.10。使われ方：N 側の未知成分の方程式の右辺を評価する。 -/
lemma dgModuleFiberBoundaryLeftPrefixCandidate_last_rhs_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    HEq ((dgModuleFiberBoundaryLeftPrefixCandidate A D f b hb).cospanOneTailRhs (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      (dgModuleFiberBoundaryRhsN A D f b hb + compose A (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) 0)
        (dgModuleFiberBoundaryUnknownA A D f b hb) (add_zero (dgModuleFiberBoundaryDegree n + 1)))
          := by
  unfold dgModuleFiberBoundaryLeftPrefixCandidate SimplexData.replaceFixed
  apply SimplexData.cospanOneTailRhs_replace_prefix_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryLeftBase A D f b) _ (dgModuleFiberBoundaryLeftBase_prefixHom A D f b)
    (cospanLastTail n) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
    rfl (dgModuleFiberBoundary_left_apex A D f b hb) (dgModuleFiberBoundary_left_N A D f b hb)
    rfl (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryRhsN A D f b hb)
    (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) 0)
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryLeftNative A D f b hb).1.property
  · exact (dgModuleFiberBoundaryRhsN_heq_raw A D f b hb).symm
  · exact dgModuleFiberBoundary_left_diagonal_heq A D f b hb

/-- 概要：Left 側候補の D 成分は挿入した生の解 d に等しい。
方針：最後の成分置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：D 成分の微分を型付きの解へ移す。 -/
lemma dgModuleFiberBoundaryLeftCandidate_last_hom {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card)
    (ha : (0 : Fin (n + 4)) =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).min' (Index.nonempty hI))
    (hc : cospanLastTail n =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).max' (Index.nonempty hI))
    (hk : dgModuleFiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).hom
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (dgModuleFiberBoundaryDegree n) hI ha hc hk = (dgModuleFiberBoundaryLeftNative A D f b
        hb).2.val := by
  unfold dgModuleFiberBoundaryLeftCandidate
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Left 側候補は N を加えた先頭集合で単体の方程式を満たす。
方針：D 成分の自己置換は右辺を変えず、先頭置換の右辺の式と δd=t a+r_D を使う。
規約：HA Proposition 1.3.1.10。使われ方：非零の未知 D 成分の方程式を完了する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_last_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation
      (insert (cospanLastTail n) (cospanPrefixFaces n)) := by
  have hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    omega
  have hk : dgModuleFiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ) := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    dsimp only [dgModuleFiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (dgModuleFiberBoundaryLeftCandidate A D f b hb)
    (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
    (dgModuleFiberBoundaryDegree n) hI (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _) hk
    rfl (dgModuleFiberBoundary_left_N A D f b hb) rfl
    (dgModuleFiberBoundaryUnknownN A D f b hb)
    (dgModuleFiberBoundaryRhsN A D f b hb + compose A (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) 0)
      (dgModuleFiberBoundaryUnknownA A D f b hb) (add_zero (dgModuleFiberBoundaryDegree n + 1)))
  · exact (heq_of_eq (dgModuleFiberBoundaryLeftCandidate_last_hom A D f b hb hI _ _ hk)).trans
      (dgModuleFiberBoundaryLeftNative A D f b hb).2.property
  · unfold dgModuleFiberBoundaryLeftCandidate
    rw [SimplexData.replaceFixed_rhs_self]
    exact dgModuleFiberBoundaryLeftPrefixCandidate_last_rhs_heq A D f b hb
  · change differential (D := RightModule A D) A
      (dgModuleFiberBoundaryUnknownN A D f b hb) = _
    rw [zero_compose, add_zero]
    exact dgModuleFiberBoundaryUnknownN_differential A D f b hb

/-- 概要：Right 側の先頭置換後の D 右辺は r_D+t a と異種等号で一致する。
方針：先頭置換による右辺の変化を共通の Hom 座標へ移す。
規約：HA Proposition 1.3.1.10。使われ方：N 側の未知成分の方程式の右辺を評価する。 -/
lemma dgModuleFiberBoundaryRightPrefixCandidate_last_rhs_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    HEq ((dgModuleFiberBoundaryRightPrefixCandidate A D f b hb).cospanOneTailRhs (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      (dgModuleFiberBoundaryRhsN A D f b hb + compose A (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) 0)
        (dgModuleFiberBoundaryUnknownA A D f b hb) (add_zero (dgModuleFiberBoundaryDegree n + 1)))
          := by
  unfold dgModuleFiberBoundaryRightPrefixCandidate SimplexData.replaceFixed
  apply SimplexData.cospanOneTailRhs_replace_prefix_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryRightBase A D f b) _ (dgModuleFiberBoundaryRightBase_prefixHom A D f b)
    (cospanLastTail n) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
    (dgModuleFiberBoundarySource_right_eq A D f b) (dgModuleFiberBoundary_right_apex A D f b hb)
    (dgModuleFiberBoundary_right_N A D f b hb)
    rfl (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryRhsN A D f b hb)
    (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) 0)
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRightNative A D f b hb).1.property
  · exact (dgModuleFiberBoundaryRhsN_heq_right A D f b hb).symm
  · exact dgModuleFiberBoundary_right_diagonal_heq A D f b hb

/-- 概要：Right 側候補の D 成分は挿入した生の解 d に等しい。
方針：最後の成分置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：D 成分の微分を型付きの解へ移す。 -/
lemma dgModuleFiberBoundaryRightCandidate_last_hom {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card)
    (ha : (0 : Fin (n + 4)) =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).min' (Index.nonempty hI))
    (hc : cospanLastTail n =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).max' (Index.nonempty hI))
    (hk : dgModuleFiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).hom
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (dgModuleFiberBoundaryDegree n) hI ha hc hk = (dgModuleFiberBoundaryRightNative A D f b
        hb).2.val := by
  unfold dgModuleFiberBoundaryRightCandidate
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Right 側候補は N を加えた先頭集合で単体の方程式を満たす。
方針：D 成分の自己置換は右辺を変えず、先頭置換の右辺の式と δd=t a+r_D を使う。
規約：HA Proposition 1.3.1.10。使われ方：非零の未知 D 成分の方程式を完了する。 -/
lemma dgModuleFiberBoundaryRightCandidate_last_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).Equation
      (insert (cospanLastTail n) (cospanPrefixFaces n)) := by
  have hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    omega
  have hk : dgModuleFiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ) := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    dsimp only [dgModuleFiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (dgModuleFiberBoundaryRightCandidate A D f b hb)
    (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
    (dgModuleFiberBoundaryDegree n) hI (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _) hk
    (dgModuleFiberBoundarySource_right_eq A D f b) (dgModuleFiberBoundary_right_N A D f b hb) rfl
    (dgModuleFiberBoundaryUnknownN A D f b hb)
    (dgModuleFiberBoundaryRhsN A D f b hb + compose A (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) 0)
      (dgModuleFiberBoundaryUnknownA A D f b hb) (add_zero (dgModuleFiberBoundaryDegree n + 1)))
  · exact (heq_of_eq (dgModuleFiberBoundaryRightCandidate_last_hom A D f b hb hI _ _ hk)).trans
      (dgModuleFiberBoundaryRightNative A D f b hb).2.property
  · unfold dgModuleFiberBoundaryRightCandidate
    rw [SimplexData.replaceFixed_rhs_self]
    exact dgModuleFiberBoundaryRightPrefixCandidate_last_rhs_heq A D f b hb
  · change differential (D := RightModule A D) A
      (dgModuleFiberBoundaryUnknownN A D f b hb) = _
    rw [zero_compose, add_zero]
    exact dgModuleFiberBoundaryUnknownN_differential A D f b hb

end SerrePositivity.InfinityCategories
