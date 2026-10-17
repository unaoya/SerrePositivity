module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryPrefixEquation
public import SerrePositivity.InfinityCategories.DGNerve.CospanPrefixReplacementTransport

/-! # 候補データの最初の脚側方程式

概要：左右の候補は B 側・C 側の未知成分を零とした方程式を満たす。
方針：先頭置換後の脚側右辺を射影の式で消し、D 側置換はこの集合に影響しないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：残る未知方程式の直接検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：最後の末尾頂点は最初の末尾頂点を加えた先頭集合に属さない。
方針：二つの末尾頂点の相違と先頭集合の上界を使う。
規約：HTT §1.2.13。使われ方：D 側置換が B 側・C 側を変えないこと。 -/
lemma cospanLast_notMem_insert_firstTail (n : ℕ) :
    cospanLastTail n ∉ insert (cospanFirstTail n) (cospanPrefixFaces n) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨ne_of_gt (cospanFirstTail_lt_lastTail n),
    cospanTail_notMem_prefix _ ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))⟩

/-- 概要：Left 側基底の先頭成分だけを明示解 a へ置き換える。
方針：固定一射の置換を先頭集合へ適用する。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換のうち脚側に影響する段階を分離する。 -/
def fiberBoundaryLeftPrefixCandidate {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) : SimplexData A (Complex A) (n + 3) :=
  (fiberBoundaryLeftBase g h b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (fiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [fiberBoundaryDegree]; push_cast; omega)
    (fiberBoundaryLeftNative g h b hb).1.val

/-- 概要：Left 側の先頭置換後の最初の脚側右辺は零。
方針：右辺の変化を型付き Hom へ移し、先頭解の射影が残差の負であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の未知成分を零に取る方程式。 -/
lemma fiberBoundaryLeftPrefixCandidate_first_rhs_zero {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftPrefixCandidate g h b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  unfold fiberBoundaryLeftPrefixCandidate SimplexData.replaceFixed
  apply SimplexData.cospanOneTailRhs_replace_prefix_zero_of_heq (A := A) (D := Complex A)
    (fiberBoundaryLeftBase g h b) _ (fiberBoundaryLeftBase_prefixHom g h b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    rfl (fiberSliceBoundary_left_apex g h b hb) (fiberSliceBoundary_left_B g h b hb)
    rfl (fiberBoundaryUnknownA g h b hb) (fiberBoundaryRhsB g h b hb)
    (Cochain.ofHom (pullbackProjectionB g h))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryLeftNative g h b hb).1.property
  · exact (fiberBoundaryRhsB_heq_raw g h b hb).symm
  · exact fiberSliceBoundary_left_projection_heq g h b hb
  · rw [Checks.complex_compose, fiberBoundaryUnknownA_projectionB]
    exact add_neg_cancel _

/-- 概要：Left 側の二成分を挿入した最終候補の最初の脚側右辺は零。
方針：D 側置換の局所性で先頭置換だけの右辺に戻す。
規約：HA Proposition 1.3.1.10。使われ方：最初の脚側方程式の右辺を消去する。 -/
lemma fiberBoundaryLeftCandidate_first_rhs_zero {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  have hnot : ¬ insert (cospanLastTail n) (cospanPrefixFaces n) ⊆
      insert (cospanFirstTail n) (cospanPrefixFaces n) := by
    intro hsub
    exact cospanLast_notMem_insert_firstTail n (hsub (Finset.mem_insert_self _ _))
  unfold fiberBoundaryLeftCandidate SimplexData.cospanOneTailRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset (hnot := hnot)]
  exact fiberBoundaryLeftPrefixCandidate_first_rhs_zero g h b hb

/-- 概要：Left 側候補は最初の末尾頂点を加えた集合の方程式を満たす。
方針：この未知成分は零であり、計算した右辺も零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知 B 側・C 側成分の方程式を完了する。 -/
lemma fiberBoundaryLeftCandidate_first_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).Equation
      (insert (cospanFirstTail n) (cospanPrefixFaces n)) := by
  have h0 : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_insert_self _ _)
  have hD : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠
      insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    exact cospanLast_notMem_insert_firstTail n (heq.symm ▸ Finset.mem_insert_self _ _)
  apply SimplexData.equation_of_fixed (fiberBoundaryLeftCandidate g h b hb)
    (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0 (cospanFirstTail n) (-(n : ℤ) - 1)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
    (cospanPrefix_insert_min _ _) (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; push_cast; omega)
  rw [fiberBoundaryLeftCandidate_unknown_zero g h b hb _ (Finset.subset_insert _ _) h0 hD]
  change differential (D := Complex A) A 0 =
    (fiberBoundaryLeftCandidate g h b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n)
  rw [fiberBoundaryLeftCandidate_first_rhs_zero]
  exact map_zero _

/-- 概要：Right 側基底の先頭成分だけを明示解 a へ置き換える。
方針：固定一射の置換を先頭集合へ適用する。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換のうち脚側に影響する段階を分離する。 -/
def fiberBoundaryRightPrefixCandidate {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) : SimplexData A (Complex A) (n + 3) :=
  (fiberBoundaryRightBase g h b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (fiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [fiberBoundaryDegree]; push_cast; omega)
    (fiberBoundaryRightNative g h b hb).1.val

/-- 概要：Right 側の先頭置換後の最初の脚側右辺は零。
方針：右辺の変化を型付き Hom へ移し、先頭解の射影が残差の負であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の未知成分を零に取る方程式。 -/
lemma fiberBoundaryRightPrefixCandidate_first_rhs_zero {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightPrefixCandidate g h b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  unfold fiberBoundaryRightPrefixCandidate SimplexData.replaceFixed
  apply SimplexData.cospanOneTailRhs_replace_prefix_zero_of_heq (A := A) (D := Complex A)
    (fiberBoundaryRightBase g h b) _ (fiberBoundaryRightBase_prefixHom g h b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_apex g h b hb)
    (fiberSliceBoundary_right_C g h b hb)
    rfl (fiberBoundaryUnknownA g h b hb) (fiberBoundaryRhsC g h b hb)
    (Cochain.ofHom (pullbackProjectionC g h))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryRightNative g h b hb).1.property
  · exact (fiberBoundaryRhsC_heq_raw g h b hb).symm
  · exact fiberSliceBoundary_right_projection_heq g h b hb
  · rw [Checks.complex_compose, fiberBoundaryUnknownA_projectionC]
    exact add_neg_cancel _

/-- 概要：Right 側の二成分を挿入した最終候補の最初の脚側右辺は零。
方針：D 側置換の局所性で先頭置換だけの右辺に戻す。
規約：HA Proposition 1.3.1.10。使われ方：最初の脚側方程式の右辺を消去する。 -/
lemma fiberBoundaryRightCandidate_first_rhs_zero {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightCandidate g h b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  have hnot : ¬ insert (cospanLastTail n) (cospanPrefixFaces n) ⊆
      insert (cospanFirstTail n) (cospanPrefixFaces n) := by
    intro hsub
    exact cospanLast_notMem_insert_firstTail n (hsub (Finset.mem_insert_self _ _))
  unfold fiberBoundaryRightCandidate SimplexData.cospanOneTailRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset (hnot := hnot)]
  exact fiberBoundaryRightPrefixCandidate_first_rhs_zero g h b hb

/-- 概要：Right 側候補は最初の末尾頂点を加えた集合の方程式を満たす。
方針：この未知成分は零であり、計算した右辺も零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知 B 側・C 側成分の方程式を完了する。 -/
lemma fiberBoundaryRightCandidate_first_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightCandidate g h b hb).Equation
      (insert (cospanFirstTail n) (cospanPrefixFaces n)) := by
  have h0 : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_insert_self _ _)
  have hD : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠
      insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    exact cospanLast_notMem_insert_firstTail n (heq.symm ▸ Finset.mem_insert_self _ _)
  apply SimplexData.equation_of_fixed (fiberBoundaryRightCandidate g h b hb)
    (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0 (cospanFirstTail n) (-(n : ℤ) - 1)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
    (cospanPrefix_insert_min _ _) (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; push_cast; omega)
  rw [fiberBoundaryRightCandidate_unknown_zero g h b hb _ (Finset.subset_insert _ _) h0 hD]
  change differential (D := Complex A) A 0 =
    (fiberBoundaryRightCandidate g h b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n)
  rw [fiberBoundaryRightCandidate_first_rhs_zero]
  exact map_zero _

end SerrePositivity.InfinityCategories.DGNerve
