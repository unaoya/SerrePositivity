module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryDEquations
public import SerrePositivity.InfinityCategories.DGNerve.CospanTriangleReplacementTransport

/-! # 候補データの全体集合の方程式

概要：左右の候補は零に取った全体集合の三角形成分の方程式を満たす。
方針：二成分の置換後の右辺を型付きの r−u a−d に移し、明示解の式で消す。
規約：HA Proposition 1.3.1.10。使われ方：候補データの全未知方程式の最後の検証。
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

/-- 概要：Left 側候補の全体集合の右辺は零。
方針：二成分置換による変化を型付き Hom に移し、明示解の三角形式で消す。
規約：HA Proposition 1.3.1.10。使われ方：零の全体成分の方程式を検証する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_full_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanTwoTailRhs = 0 := by
  unfold dgModuleFiberBoundaryLeftCandidate SimplexData.replaceFixed
  apply SimplexData.cospanTwoTailRhs_replace_zero_of_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryLeftBase A D f b) _ _ (dgModuleFiberBoundaryLeftBase_prefixHom A D f b) _
    rfl (dgModuleFiberBoundary_left_apex A D f b hb) (dgModuleFiberBoundary_left_N A D f b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryUnknownN A D f b hb)
    (dgModuleFiberBoundaryRhsMN A D f b hb) (dgModuleFiberNullHomotopy A D f)
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryLeftNative A D f b hb).1.property
  · unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_same]
    exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryLeftNative A D f b hb).2.property
  · exact (dgModuleFiberBoundaryRhsMN_heq_raw A D f b hb).symm
  · exact dgModuleFiberBoundary_left_homotopy_heq A D f b hb
  · have hs (r a d : GradedHom A (dgModuleFiberBoundarySource A D f b)
        (ForgetEnrichment.to (Complex A) N) (dgModuleFiberBoundaryDegree n)) :
        r - a - d = -d - a + r := by abel
    exact (hs _ _ _).trans (dgModuleFiberBoundaryUnknown_left_triangle A D f b hb).symm
  · have hne : insert (cospanLastTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
      intro heq
      exact cospanTail_notMem_prefix _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
        (heq ▸ Finset.mem_insert_self _ _)
    unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_of_ne (hne := hne)]
    exact dgModuleFiberBoundaryLeftBase_unknownHom A D f b _ (Finset.subset_insert _ _) _ _ _ _ _
      _ _

/-- 概要：Left 側候補は全体集合で単体の方程式を満たす。
方針：全体成分は零に保たれており、二置換の公式から右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：全体集合の未知方程式を完了する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_full_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation Finset.univ := by
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
  apply SimplexData.equation_of_fixed (dgModuleFiberBoundaryLeftCandidate A D f b hb)
    Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [dgModuleFiberBoundaryLeftCandidate_unknown_zero A D f b hb _ (Finset.subset_univ _) h0 hD]
  change differential (D := RightModule A D) A 0 =
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanTwoTailRhs
  rw [dgModuleFiberBoundaryLeftCandidate_full_rhs_zero]
  exact map_zero _

/-- 概要：Right 側候補の全体集合の右辺は零。
方針：二成分置換による変化を型付き Hom に移し、明示解の三角形式で消す。
規約：HA Proposition 1.3.1.10。使われ方：零の全体成分の方程式を検証する。 -/
lemma dgModuleFiberBoundaryRightCandidate_full_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).cospanTwoTailRhs = 0 := by
  unfold dgModuleFiberBoundaryRightCandidate SimplexData.replaceFixed
  apply SimplexData.cospanTwoTailRhs_replace_zero_of_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryRightBase A D f b) _ _ (dgModuleFiberBoundaryRightBase_prefixHom A D f
      b) _
    (dgModuleFiberBoundarySource_right_eq A D f b) (dgModuleFiberBoundary_right_apex A D f b hb)
    (dgModuleFiberBoundary_right_N A D f b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryUnknownN A D f b hb)
    (dgModuleFiberBoundaryRhsZeroN A D f b hb) (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) N) (-1))
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRightNative A D f b hb).1.property
  · unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_same]
    exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRightNative A D f b hb).2.property
  · exact (dgModuleFiberBoundaryRhsZeroN_heq_raw A D f b hb).symm
  · exact dgModuleFiberBoundary_right_homotopy_heq A D f b hb
  · rw [zero_compose, sub_zero]
    unfold dgModuleFiberBoundaryUnknownN
    exact sub_self _
  · have hne : insert (cospanLastTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
      intro heq
      exact cospanTail_notMem_prefix _
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
        (heq ▸ Finset.mem_insert_self _ _)
    unfold SimplexData.cospanTriangleD_Hom
    rw [SimplexData.replace_hom_of_ne (hne := hne)]
    exact dgModuleFiberBoundaryRightBase_unknownHom A D f b _ (Finset.subset_insert _ _) _ _ _ _ _
      _ _

/-- 概要：Right 側候補は全体集合で単体の方程式を満たす。
方針：全体成分は零に保たれており、二置換の公式から右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：全体集合の未知方程式を完了する。 -/
lemma dgModuleFiberBoundaryRightCandidate_full_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).Equation Finset.univ := by
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
  apply SimplexData.equation_of_fixed (dgModuleFiberBoundaryRightCandidate A D f b hb)
    Finset.univ 0 (cospanLastTail n) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (HornData.univ_min_zero (n + 1) _) (HornData.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)
  rw [dgModuleFiberBoundaryRightCandidate_unknown_zero A D f b hb _ (Finset.subset_univ _) h0 hD]
  change differential (D := RightModule A D) A 0 =
    (dgModuleFiberBoundaryRightCandidate A D f b hb).cospanTwoTailRhs
  rw [dgModuleFiberBoundaryRightCandidate_full_rhs_zero]
  exact map_zero _

end SerrePositivity.InfinityCategories
