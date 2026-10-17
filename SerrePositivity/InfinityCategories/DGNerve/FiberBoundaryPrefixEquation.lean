module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryCandidateKnown
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # 候補データの先頭集合の方程式

概要：明示解を挿入した候補は先頭集合で単体の方程式を満たす。
方針：先頭右辺は二回の置換で変わらず、成分の微分は型付き解の微分式へ移す。
規約：HA Proposition 1.3.1.10。使われ方：四つの未知集合のうち最初の方程式の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：D を加えた先頭集合は先頭集合に含まれない。
方針：D の頂点番号は先頭の最大値より大きい。
規約：HTT §1.2.13。使われ方：D 側成分の挿入が先頭の方程式を変えないこと。 -/
lemma cospanPrefix_insertLast_not_subset (n : ℕ) :
    ¬ insert (cospanLastTail n) (cospanPrefixFaces n) ⊆ cospanPrefixFaces n := by
  intro hsub
  have hle := (mem_cospanPrefixFaces_iff_le _).mp (hsub (Finset.mem_insert_self _ _))
  exact not_le_of_gt ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) hle

/-- 概要：Left 側候補の先頭成分は挿入した生の解に等しい。
方針：D 側集合との相違と先頭置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭成分の微分の同定。 -/
lemma fiberBoundaryLeftCandidate_prefix_hom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : fiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (fiberBoundaryLeftCandidate g h b hb).hom (cospanPrefixFaces n) 0 (cospanApex n)
      (fiberBoundaryDegree n + 1) hI ha hc hk = (fiberBoundaryLeftNative g h b hb).1.val := by
  have hne : cospanPrefixFaces n ≠ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    apply cospanPrefix_insertLast_not_subset n
    rw [← heq]
  unfold fiberBoundaryLeftCandidate
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne]
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Left 側候補の先頭右辺は零未知基底の先頭右辺から変わらない。
方針：D 側置換の局所性と先頭置換の自己右辺の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付きの r₀ をそのまま先頭方程式に使う。 -/
lemma fiberBoundaryLeftCandidate_prefix_rhs {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : fiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (fiberBoundaryLeftCandidate g h b hb).rhs (cospanPrefixFaces n) 0 (cospanApex n)
      (fiberBoundaryDegree n + 1) hI ha hc hk =
      (fiberBoundaryLeftBase g h b).rhs (cospanPrefixFaces n) 0 (cospanApex n)
        (fiberBoundaryDegree n + 1) hI ha hc hk := by
  unfold fiberBoundaryLeftCandidate
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (cospanPrefix_insertLast_not_subset n)]
  exact SimplexData.replaceFixed_rhs_self _ _ _ _ _ _ _ _ _ _

/-- 概要：Left 側候補は先頭集合で単体の方程式を満たす。
方針：保存された右辺と挿入した成分を型付き r₀,a へ異種等号で移し、δa=r₀ を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭の未知方程式の検証。 -/
lemma fiberBoundaryLeftCandidate_prefix_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).Equation (cospanPrefixFaces n) := by
  have hI : 2 ≤ (cospanPrefixFaces n).card := by rw [card_cospanPrefixFaces]; omega
  have hk : fiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ) := by
    rw [card_cospanPrefixFaces]
    dsimp only [fiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (fiberBoundaryLeftCandidate g h b hb)
    (cospanPrefixFaces n) 0 (cospanApex n)
    (fiberBoundaryDegree n + 1) hI (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) hk
    rfl (fiberSliceBoundary_left_apex g h b hb) rfl
    (fiberBoundaryUnknownA g h b hb) (fiberBoundaryRhs0 g h b hb)
  · exact (heq_of_eq (fiberBoundaryLeftCandidate_prefix_hom g h b hb hI _ _ hk)).trans
      (fiberBoundaryLeftNative g h b hb).1.property
  · rw [fiberBoundaryLeftCandidate_prefix_rhs g h b hb hI _ _ hk]
    exact ((fiberBoundaryLeftBase g h b).rhs_heq_of_degrees _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryRhs0_heq_raw g h b hb).symm
  · exact fiberBoundaryUnknownA_differential g h b hb

/-- 概要：Right 側候補の先頭成分は挿入した生の解に等しい。
方針：D 側集合との相違と先頭置換の自己評価を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭成分の微分の同定。 -/
lemma fiberBoundaryRightCandidate_prefix_hom {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : fiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (fiberBoundaryRightCandidate g h b hb).hom (cospanPrefixFaces n) 0 (cospanApex n)
      (fiberBoundaryDegree n + 1) hI ha hc hk = (fiberBoundaryRightNative g h b hb).1.val := by
  have hne : cospanPrefixFaces n ≠ insert (cospanLastTail n) (cospanPrefixFaces n) := by
    intro heq
    apply cospanPrefix_insertLast_not_subset n
    rw [← heq]
  unfold fiberBoundaryRightCandidate
  rw [SimplexData.replaceFixed_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne]
  exact SimplexData.replaceFixed_hom_same _ _ _ _ _ _ _ _ _ _

/-- 概要：Right 側候補の先頭右辺は零未知基底の先頭右辺から変わらない。
方針：D 側置換の局所性と先頭置換の自己右辺の保存を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付きの r₀ をそのまま先頭方程式に使う。 -/
lemma fiberBoundaryRightCandidate_prefix_rhs {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (hI : 2 ≤ (cospanPrefixFaces n).card)
    (ha : (0 : Fin (n + 4)) = (cospanPrefixFaces n).min' (Index.nonempty hI))
    (hc : cospanApex n = (cospanPrefixFaces n).max' (Index.nonempty hI))
    (hk : fiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ)) :
    (fiberBoundaryRightCandidate g h b hb).rhs (cospanPrefixFaces n) 0 (cospanApex n)
      (fiberBoundaryDegree n + 1) hI ha hc hk =
      (fiberBoundaryRightBase g h b).rhs (cospanPrefixFaces n) 0 (cospanApex n)
        (fiberBoundaryDegree n + 1) hI ha hc hk := by
  unfold fiberBoundaryRightCandidate
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (cospanPrefix_insertLast_not_subset n)]
  exact SimplexData.replaceFixed_rhs_self _ _ _ _ _ _ _ _ _ _

/-- 概要：Right 側候補は先頭集合で単体の方程式を満たす。
方針：保存された右辺と挿入した成分を型付き r₀,a へ異種等号で移し、δa=r₀ を使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭の未知方程式の検証。 -/
lemma fiberBoundaryRightCandidate_prefix_equation {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryRightCandidate g h b hb).Equation (cospanPrefixFaces n) := by
  have hI : 2 ≤ (cospanPrefixFaces n).card := by rw [card_cospanPrefixFaces]; omega
  have hk : fiberBoundaryDegree n + 1 = 2 - ((cospanPrefixFaces n).card : ℤ) := by
    rw [card_cospanPrefixFaces]
    dsimp only [fiberBoundaryDegree]
    push_cast
    omega
  apply SimplexData.equation_of_fixed_heq (fiberBoundaryRightCandidate g h b hb)
    (cospanPrefixFaces n) 0 (cospanApex n)
    (fiberBoundaryDegree n + 1) hI (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) hk
    (fiberBoundarySource_right_eq g h b) (fiberSliceBoundary_right_apex g h b hb) rfl
    (fiberBoundaryUnknownA g h b hb) (fiberBoundaryRhs0 g h b hb)
  · exact (heq_of_eq (fiberBoundaryRightCandidate_prefix_hom g h b hb hI _ _ hk)).trans
      (fiberBoundaryRightNative g h b hb).1.property
  · rw [fiberBoundaryRightCandidate_prefix_rhs g h b hb hI _ _ hk]
    exact ((fiberBoundaryRightBase g h b).rhs_heq_of_degrees _ _ _ _ _ _ _ _ _ _).trans
      (fiberBoundaryRhs0_heq_right g h b hb).symm
  · exact fiberBoundaryUnknownA_differential g h b hb

end SerrePositivity.InfinityCategories.DGNerve
