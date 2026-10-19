module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryPrefixEquation
public import SerrePositivity.InfinityCategories.DGNerve.CospanPrefixReplacementTransport

/-! # 候補データの最初の脚側方程式

概要：左右の候補は M 側・零角側の未知成分を零とした方程式を満たす。
方針：先頭置換後の脚側右辺を射影の式で消し、N 側置換はこの集合に影響しないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：残る未知方程式の直接検証。
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

/-- 零角への射影との合成は零残差の負。 -/
lemma dgModuleFiberBoundaryUnknownA_projectionZero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    compose A (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) (moduleZero A D)) 0)
      (dgModuleFiberBoundaryUnknownA A D f b hb)
      (add_zero (dgModuleFiberBoundaryDegree n + 1)) =
      -dgModuleFiberBoundaryRhsZero A D f b hb := by
  rw [zero_compose, dgModuleFiberBoundaryRhsZero_eq_zero, neg_zero]

/-- 概要：最後の末尾頂点は最初の末尾頂点を加えた先頭集合に属さない。
方針：二つの末尾頂点の相違と先頭集合の上界を使う。
規約：HTT §1.2.13。使われ方：N 側置換が M 側・零角側を変えないこと。 -/
lemma cospanLast_notMem_insert_firstTail (n : ℕ) :
    cospanLastTail n ∉ insert (cospanFirstTail n) (cospanPrefixFaces n) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨ne_of_gt (cospanFirstTail_lt_lastTail n),
    cospanTail_notMem_prefix _ ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))⟩

/-- 概要：Left 側基底の先頭成分だけを明示解 a へ置き換える。
方針：固定一射の置換を先頭集合へ適用する。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換のうち脚側に影響する段階を分離する。 -/
def dgModuleFiberBoundaryLeftPrefixCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) : SimplexData A (RightModule A D) (n + 3) :=
  (dgModuleFiberBoundaryLeftBase A D f b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (dgModuleFiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [dgModuleFiberBoundaryDegree]; push_cast; omega)
    (dgModuleFiberBoundaryLeftNative A D f b hb).1.val

/-- 概要：Left 側の先頭置換後の最初の脚側右辺は零。
方針：右辺の変化を型付き Hom へ移し、先頭解の射影が残差の負であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の未知成分を零に取る方程式。 -/
lemma dgModuleFiberBoundaryLeftPrefixCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftPrefixCandidate A D f b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  unfold dgModuleFiberBoundaryLeftPrefixCandidate SimplexData.replaceFixed
  apply SimplexData.cospanOneTailRhs_replace_prefix_zero_of_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryLeftBase A D f b) _ (dgModuleFiberBoundaryLeftBase_prefixHom A D f b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    rfl (dgModuleFiberBoundary_left_apex A D f b hb) (dgModuleFiberBoundary_left_M A D f b hb)
    rfl (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryRhsM A D f b hb)
    (dgModuleFiberProjectionElement A D f)
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryLeftNative A D f b hb).1.property
  · exact (dgModuleFiberBoundaryRhsM_heq_raw A D f b hb).symm
  · exact dgModuleFiberBoundary_left_projection_heq A D f b hb
  · rw [dgModuleFiberBoundaryUnknownA_projection]
    exact add_neg_cancel _

/-- 概要：Left 側の二成分を挿入した最終候補の最初の脚側右辺は零。
方針：N 側置換の局所性で先頭置換だけの右辺に戻す。
規約：HA Proposition 1.3.1.10。使われ方：最初の脚側方程式の右辺を消去する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  have hnot : ¬ insert (cospanLastTail n) (cospanPrefixFaces n) ⊆
      insert (cospanFirstTail n) (cospanPrefixFaces n) := by
    intro hsub
    exact cospanLast_notMem_insert_firstTail n (hsub (Finset.mem_insert_self _ _))
  unfold dgModuleFiberBoundaryLeftCandidate SimplexData.cospanOneTailRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset (hnot := hnot)]
  exact dgModuleFiberBoundaryLeftPrefixCandidate_first_rhs_zero A D f b hb

/-- 概要：Left 側候補は最初の末尾頂点を加えた集合の方程式を満たす。
方針：この未知成分は零であり、計算した右辺も零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知 M 側・零角側成分の方程式を完了する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation
      (insert (cospanFirstTail n) (cospanPrefixFaces n)) := by
  have h0 : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_insert_self _ _)
  have hD : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠
      insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    exact cospanLast_notMem_insert_firstTail n (heq.symm ▸ Finset.mem_insert_self _ _)
  apply SimplexData.equation_of_fixed (dgModuleFiberBoundaryLeftCandidate A D f b hb)
    (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0 (cospanFirstTail n) (-(n : ℤ) - 1)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
    (cospanPrefix_insert_min _ _) (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; push_cast; omega)
  rw [dgModuleFiberBoundaryLeftCandidate_unknown_zero A D f b hb _ (Finset.subset_insert _ _) h0 hD]
  change differential (D := RightModule A D) A 0 =
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n)
  rw [dgModuleFiberBoundaryLeftCandidate_first_rhs_zero]
  exact map_zero _

/-- 概要：Right 側基底の先頭成分だけを明示解 a へ置き換える。
方針：固定一射の置換を先頭集合へ適用する。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換のうち脚側に影響する段階を分離する。 -/
def dgModuleFiberBoundaryRightPrefixCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) : SimplexData A (RightModule A D) (n + 3) :=
  (dgModuleFiberBoundaryRightBase A D f b).replaceFixed (cospanPrefixFaces n) 0 (cospanApex n)
    (dgModuleFiberBoundaryDegree n + 1)
    (by rw [card_cospanPrefixFaces]; omega)
    (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _)
    (by rw [card_cospanPrefixFaces]; dsimp only [dgModuleFiberBoundaryDegree]; push_cast; omega)
    (dgModuleFiberBoundaryRightNative A D f b hb).1.val

/-- 概要：Right 側の先頭置換後の最初の脚側右辺は零。
方針：右辺の変化を型付き Hom へ移し、先頭解の射影が残差の負であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の未知成分を零に取る方程式。 -/
lemma dgModuleFiberBoundaryRightPrefixCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightPrefixCandidate A D f b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  unfold dgModuleFiberBoundaryRightPrefixCandidate SimplexData.replaceFixed
  apply SimplexData.cospanOneTailRhs_replace_prefix_zero_of_heq (A := A) (D := RightModule A D)
    (dgModuleFiberBoundaryRightBase A D f b) _ (dgModuleFiberBoundaryRightBase_prefixHom A D f b)
    (cospanFirstTail n) (cospanApex_lt_firstTail n)
    (dgModuleFiberBoundarySource_right_eq A D f b) (dgModuleFiberBoundary_right_apex A D f b hb)
    (dgModuleFiberBoundary_right_zero A D f b hb)
    rfl (dgModuleFiberBoundaryUnknownA A D f b hb) (dgModuleFiberBoundaryRhsZero A D f b hb)
    (0 : GradedHom A (dgModuleFiber A D f)
      (ForgetEnrichment.to (Complex A) (moduleZero A D)) 0)
  · exact (SimplexData.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRightNative A D f b hb).1.property
  · exact (dgModuleFiberBoundaryRhsZero_heq_raw A D f b hb).symm
  · exact dgModuleFiberBoundary_right_projection_heq A D f b hb
  · rw [dgModuleFiberBoundaryUnknownA_projectionZero]
    exact add_neg_cancel _

/-- 概要：Right 側の二成分を挿入した最終候補の最初の脚側右辺は零。
方針：N 側置換の局所性で先頭置換だけの右辺に戻す。
規約：HA Proposition 1.3.1.10。使われ方：最初の脚側方程式の右辺を消去する。 -/
lemma dgModuleFiberBoundaryRightCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n) = 0 := by
  have hnot : ¬ insert (cospanLastTail n) (cospanPrefixFaces n) ⊆
      insert (cospanFirstTail n) (cospanPrefixFaces n) := by
    intro hsub
    exact cospanLast_notMem_insert_firstTail n (hsub (Finset.mem_insert_self _ _))
  unfold dgModuleFiberBoundaryRightCandidate SimplexData.cospanOneTailRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset (hnot := hnot)]
  exact dgModuleFiberBoundaryRightPrefixCandidate_first_rhs_zero A D f b hb

/-- 概要：Right 側候補は最初の末尾頂点を加えた集合の方程式を満たす。
方針：この未知成分は零であり、計算した右辺も零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知 M 側・零角側成分の方程式を完了する。 -/
lemma dgModuleFiberBoundaryRightCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightCandidate A D f b hb).Equation
      (insert (cospanFirstTail n) (cospanPrefixFaces n)) := by
  have h0 : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠ cospanPrefixFaces n := by
    intro heq
    exact cospanTail_notMem_prefix _ (cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_insert_self _ _)
  have hD : insert (cospanFirstTail n) (cospanPrefixFaces n) ≠
      insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    exact cospanLast_notMem_insert_firstTail n (heq.symm ▸ Finset.mem_insert_self _ _)
  apply SimplexData.equation_of_fixed (dgModuleFiberBoundaryRightCandidate A D f b hb)
    (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0 (cospanFirstTail n) (-(n : ℤ) - 1)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
    (cospanPrefix_insert_min _ _) (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _)
    (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; push_cast; omega)
  rw [dgModuleFiberBoundaryRightCandidate_unknown_zero A D f b hb _ (Finset.subset_insert _ _) h0
    hD]
  change differential (D := RightModule A D) A 0 =
    (dgModuleFiberBoundaryRightCandidate A D f b hb).cospanOneTailRhs
      (cospanFirstTail n) (cospanApex_lt_firstTail n)
  rw [dgModuleFiberBoundaryRightCandidate_first_rhs_zero]
  exact map_zero _

end SerrePositivity.InfinityCategories
