module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryDEquations
public import SerrePositivity.InfinityCategories.DGNerve.CospanTriangleReplacementTransport

/-! # 候補データの全体集合の方程式

概要：左右の候補は零に取った全体集合の三角形成分の方程式を満たす。
方針：二成分の置換後の右辺を型付きの r−u a−d に移し、明示解の式で消す。
規約：HA Proposition 1.3.1.10。使われ方：候補データの全未知方程式の最後の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：Left 側候補の全体集合の右辺は零。
方針：二成分置換による変化を型付き Hom に移し、明示解の三角形式で消す。
規約：HA Proposition 1.3.1.10。使われ方：零の全体成分の方程式を検証する。 -/
lemma fiberBoundaryLeftCandidate_full_rhs_zero {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).cospanTwoTailRhs = 0 := by
  unfold fiberBoundaryLeftCandidate SimplexData.replaceFixed
  apply SimplexData.cospanTwoTailRhs_replace_zero_of_heq (A := A) (D := Complex A)
    (fiberBoundaryLeftBase g h b) _ _ (fiberBoundaryLeftBase_prefixHom g h b) _
    rfl (fiberSliceBoundary_left_apex g h b hb) (fiberSliceBoundary_left_D g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    (fiberBoundaryUnknownA g h b hb) (fiberBoundaryUnknownD g h b hb)
    (fiberBoundaryRhsBD g h b hb) (fiberNullHomotopy (fiberDifference g h))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryLeftNative g h b hb).1.property
  · unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_same]
    exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryLeftNative g h b hb).2.property
  · exact (fiberBoundaryRhsBD_heq_raw g h b hb).symm
  · exact fiberSliceBoundary_left_homotopy_heq g h b hb
  · rw [Checks.complex_compose]
    have hs (r a d : Cochain (fiberBoundarySource g h b) D (fiberBoundaryDegree n)) :
        r - a - d = -d - a + r := by abel
    exact (hs _ _ _).trans (fiberBoundaryUnknown_left_triangle g h b hb).symm
  · have hne : insert (cospanLastTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
      intro heq
      exact cospanTail_notMem_prefix _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
        (heq ▸ Finset.mem_insert_self _ _)
    unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_of_ne (hne := hne)]
    exact fiberBoundaryLeftBase_unknownHom g h b _ (Finset.subset_insert _ _) _ _ _ _ _ _ _

/-- 概要：Left 側候補は全体集合で単体の方程式を満たす。
方針：全体成分は零に保たれており、二置換の公式から右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：全体集合の未知方程式を完了する。 -/
lemma fiberBoundaryLeftCandidate_full_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).Equation Finset.univ := by
  have h0 : (Finset.univ : Finset (Fin (n + 4))) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_univ _)
  have hD : (Finset.univ : Finset (Fin (n + 4))) ≠
      insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    have hmem := heq ▸ (Finset.mem_univ (cospanFirstTail n))
    rcases Finset.mem_insert.mp hmem with hfirst | hprefix
    · exact ne_of_lt (cospanFirstTail_lt_lastTail n) hfirst
    · exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n) hprefix
  apply SimplexData.equation_of_fixed (fiberBoundaryLeftCandidate g h b hb)
    Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [fiberBoundaryLeftCandidate_unknown_zero g h b hb _ (Finset.subset_univ _) h0 hD]
  change differential (D := Complex A) A 0 =
    (fiberBoundaryLeftCandidate g h b hb).cospanTwoTailRhs
  rw [fiberBoundaryLeftCandidate_full_rhs_zero]
  exact map_zero _

/-- 概要：Right 側候補の全体集合の右辺は零。
方針：二成分置換による変化を型付き Hom に移し、明示解の三角形式で消す。
規約：HA Proposition 1.3.1.10。使われ方：零の全体成分の方程式を検証する。 -/
lemma fiberBoundaryRightCandidate_full_rhs_zero {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightCandidate g h b hb).cospanTwoTailRhs = 0 := by
  unfold fiberBoundaryRightCandidate SimplexData.replaceFixed
  apply SimplexData.cospanTwoTailRhs_replace_zero_of_heq (A := A) (D := Complex A)
    (fiberBoundaryRightBase g h b) _ _ (fiberBoundaryRightBase_prefixHom g h b) _
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_apex g h b hb)
    (fiberSliceBoundary_right_D g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    (fiberBoundaryUnknownA g h b hb) (fiberBoundaryUnknownD g h b hb)
    (fiberBoundaryRhsCD g h b hb) (0 : Cochain (pullbackFiber g h) D (-1))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryRightNative g h b hb).1.property
  · unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_same]
    exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryRightNative g h b hb).2.property
  · exact (fiberBoundaryRhsCD_heq_raw g h b hb).symm
  · exact fiberSliceBoundary_right_homotopy_heq g h b hb
  · rw [zero_compose, sub_zero]
    unfold fiberBoundaryUnknownD
    exact sub_self _
  · have hne : insert (cospanLastTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
      intro heq
      exact cospanTail_notMem_prefix _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
        (heq ▸ Finset.mem_insert_self _ _)
    unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_of_ne (hne := hne)]
    exact fiberBoundaryRightBase_unknownHom g h b _ (Finset.subset_insert _ _) _ _ _ _ _ _ _

/-- 概要：Right 側候補は全体集合で単体の方程式を満たす。
方針：全体成分は零に保たれており、二置換の公式から右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：全体集合の未知方程式を完了する。 -/
lemma fiberBoundaryRightCandidate_full_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightCandidate g h b hb).Equation Finset.univ := by
  have h0 : (Finset.univ : Finset (Fin (n + 4))) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_univ _)
  have hD : (Finset.univ : Finset (Fin (n + 4))) ≠
      insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    have hmem := heq ▸ (Finset.mem_univ (cospanFirstTail n))
    rcases Finset.mem_insert.mp hmem with hfirst | hprefix
    · exact ne_of_lt (cospanFirstTail_lt_lastTail n) hfirst
    · exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n) hprefix
  apply SimplexData.equation_of_fixed (fiberBoundaryRightCandidate g h b hb)
    Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [fiberBoundaryRightCandidate_unknown_zero g h b hb _ (Finset.subset_univ _) h0 hD]
  change differential (D := Complex A) A 0 =
    (fiberBoundaryRightCandidate g h b hb).cospanTwoTailRhs
  rw [fiberBoundaryRightCandidate_full_rhs_zero]
  exact map_zero _

end SerrePositivity.InfinityCategories.DGNerve
