module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryLegEquations

/-! # 候補データの D 側方程式

概要：非零の D 側成分 d を入れた左右の候補は、その未知集合の微分方程式を満たす。
方針：先頭置換による右辺の変化を対角射の合成と同定し、δd=t a+r_D を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残る検証を全体集合の三角形方程式に限定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：Left 側の先頭置換後の D 右辺は r_D+t a と異種等号で一致する。
方針：先頭置換による右辺の変化を共通の Hom 座標へ移す。
規約：HA Proposition 1.3.1.10。使われ方：D 側の未知成分の方程式の右辺を評価する。 -/
lemma fiberBoundaryLeftPrefixCandidate_last_rhs_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((fiberBoundaryLeftPrefixCandidate g h b hb).cospanOneTailRhs (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      (fiberBoundaryRhsD g h b hb + (fiberBoundaryUnknownA g h b hb).comp
        (Cochain.ofHom (pullbackDiagonal g h)) (add_zero (fiberBoundaryDegree n + 1))) := by
  unfold fiberBoundaryLeftPrefixCandidate SimplexData.replaceFixed
  rw [← Checks.complex_compose]
  apply SimplexData.cospanOneTailRhs_replace_prefix_heq (A := A) (D := Complex A)
    (fiberBoundaryLeftBase g h b) _ (fiberBoundaryLeftBase_prefixHom g h b)
    (cospanLastTail n) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
    rfl (fiberSliceBoundary_left_apex g h b hb) (fiberSliceBoundary_left_D g h b hb)
    rfl (fiberBoundaryUnknownA g h b hb) (fiberBoundaryRhsD g h b hb)
    (Cochain.ofHom (pullbackDiagonal g h))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryLeftNative g h b hb).1.property
  · exact (fiberBoundaryRhsD_heq_raw g h b hb).symm
  · exact fiberSliceBoundary_left_diagonal_heq g h b hb

/-- 概要：Left 側候補の D 成分は挿入した生の解 d に等しい。
方針：最後の成分置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：D 成分の微分を型付きの解へ移す。 -/
lemma fiberBoundaryLeftCandidate_last_hom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card)
    (ha : (0 : Fin (n + 4)) =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).min' (Index.nonempty hI))
    (hc : cospanLastTail n =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).max' (Index.nonempty hI))
    (hk : fiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ)) :
    (fiberBoundaryLeftCandidate g h b hb).hom
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (fiberBoundaryDegree n) hI ha hc hk = (fiberBoundaryLeftNative g h b hb).2.val := by
  unfold fiberBoundaryLeftCandidate
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Left 側候補は D を加えた先頭集合で単体の方程式を満たす。
方針：D 成分の自己置換は右辺を変えず、先頭置換の右辺の式と δd=t a+r_D を使う。
規約：HA Proposition 1.3.1.10。使われ方：非零の未知 D 成分の方程式を完了する。 -/
lemma fiberBoundaryLeftCandidate_last_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).Equation
      (insert (cospanLastTail n) (cospanPrefixFaces n)) := by
  have hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    omega
  have hk : fiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ) := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    dsimp only [fiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (fiberBoundaryLeftCandidate g h b hb)
    (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
    (fiberBoundaryDegree n) hI (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _) hk
    rfl (fiberSliceBoundary_left_D g h b hb) rfl
    (fiberBoundaryUnknownD g h b hb)
    (fiberBoundaryRhsD g h b hb + (fiberBoundaryUnknownA g h b hb).comp
      (Cochain.ofHom (pullbackDiagonal g h)) (add_zero (fiberBoundaryDegree n + 1)))
  · exact (heq_of_eq (fiberBoundaryLeftCandidate_last_hom g h b hb hI _ _ hk)).trans
      (fiberBoundaryLeftNative g h b hb).2.property
  · unfold fiberBoundaryLeftCandidate
    rw [SimplexData.replaceFixed_rhs_self]
    exact fiberBoundaryLeftPrefixCandidate_last_rhs_heq g h b hb
  · exact (fiberBoundaryUnknownD_differential g h b hb).trans (add_comm _ _)

/-- 概要：Right 側の先頭置換後の D 右辺は r_D+t a と異種等号で一致する。
方針：先頭置換による右辺の変化を共通の Hom 座標へ移す。
規約：HA Proposition 1.3.1.10。使われ方：D 側の未知成分の方程式の右辺を評価する。 -/
lemma fiberBoundaryRightPrefixCandidate_last_rhs_heq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    HEq ((fiberBoundaryRightPrefixCandidate g h b hb).cospanOneTailRhs (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)))
      (fiberBoundaryRhsD g h b hb + (fiberBoundaryUnknownA g h b hb).comp
        (Cochain.ofHom (pullbackDiagonal g h)) (add_zero (fiberBoundaryDegree n + 1))) := by
  unfold fiberBoundaryRightPrefixCandidate SimplexData.replaceFixed
  rw [← Checks.complex_compose]
  apply SimplexData.cospanOneTailRhs_replace_prefix_heq (A := A) (D := Complex A)
    (fiberBoundaryRightBase g h b) _ (fiberBoundaryRightBase_prefixHom g h b)
    (cospanLastTail n) ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_apex g h b hb)
    (fiberSliceBoundary_right_D g h b hb)
    rfl (fiberBoundaryUnknownA g h b hb) (fiberBoundaryRhsD g h b hb)
    (Cochain.ofHom (pullbackDiagonal g h))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryRightNative g h b hb).1.property
  · exact (fiberBoundaryRhsD_heq_right g h b hb).symm
  · exact fiberSliceBoundary_right_diagonal_heq g h b hb

/-- 概要：Right 側候補の D 成分は挿入した生の解 d に等しい。
方針：最後の成分置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：D 成分の微分を型付きの解へ移す。 -/
lemma fiberBoundaryRightCandidate_last_hom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card)
    (ha : (0 : Fin (n + 4)) =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).min' (Index.nonempty hI))
    (hc : cospanLastTail n =
      (insert (cospanLastTail n) (cospanPrefixFaces n)).max' (Index.nonempty hI))
    (hk : fiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ)) :
    (fiberBoundaryRightCandidate g h b hb).hom
      (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
      (fiberBoundaryDegree n) hI ha hc hk = (fiberBoundaryRightNative g h b hb).2.val := by
  unfold fiberBoundaryRightCandidate
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Right 側候補は D を加えた先頭集合で単体の方程式を満たす。
方針：D 成分の自己置換は右辺を変えず、先頭置換の右辺の式と δd=t a+r_D を使う。
規約：HA Proposition 1.3.1.10。使われ方：非零の未知 D 成分の方程式を完了する。 -/
lemma fiberBoundaryRightCandidate_last_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightCandidate g h b hb).Equation
      (insert (cospanLastTail n) (cospanPrefixFaces n)) := by
  have hI : 2 ≤ (insert (cospanLastTail n) (cospanPrefixFaces n)).card := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    omega
  have hk : fiberBoundaryDegree n =
      2 - ((insert (cospanLastTail n) (cospanPrefixFaces n)).card : ℤ) := by
    rw [card_cospanPrefix_insert _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
    dsimp only [fiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (fiberBoundaryRightCandidate g h b hb)
    (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
    (fiberBoundaryDegree n) hI (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _) hk
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_D g h b hb) rfl
    (fiberBoundaryUnknownD g h b hb)
    (fiberBoundaryRhsD g h b hb + (fiberBoundaryUnknownA g h b hb).comp
      (Cochain.ofHom (pullbackDiagonal g h)) (add_zero (fiberBoundaryDegree n + 1)))
  · exact (heq_of_eq (fiberBoundaryRightCandidate_last_hom g h b hb hI _ _ hk)).trans
      (fiberBoundaryRightNative g h b hb).2.property
  · unfold fiberBoundaryRightCandidate
    rw [SimplexData.replaceFixed_rhs_self]
    exact fiberBoundaryRightPrefixCandidate_last_rhs_heq g h b hb
  · exact (fiberBoundaryUnknownD_differential g h b hb).trans (add_comm _ _)

end SerrePositivity.InfinityCategories.DGNerve
