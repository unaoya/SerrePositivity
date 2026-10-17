module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryCandidateComponents

/-! # 標準 fiber の左右の充填単体の共通面

概要：左右の明示解を挿入した単体は先頭と D からなる共通面で一致する。
方針：挿入成分は共通の型付き解と比較し、それ以外は零未知基底の一致へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二つの標準セルの貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：左右の候補データは共通面へ制限すると等しい。
方針：対象を元の共通面から同定し、二つの挿入集合と残りの集合を分けて成分を比較する。
規約：HA Proposition 1.3.1.10。使われ方：左右の単体を貼るための整合条件。 -/
lemma fiberBoundaryCandidate_common {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftCandidate g h b hb).pullback (cospanCommonOrderHom n) =
      (fiberBoundaryRightCandidate g h b hb).pullback (cospanCommonOrderHom n) := by
  have hi : Function.Injective (cospanCommonOrderHom n) :=
    (cospanFirstTail n).succAboveOrderEmb.injective
  have hbase : (fiberBoundaryLeftBase g h b).pullback (cospanCommonOrderHom n) =
      (fiberBoundaryRightBase g h b).pullback (cospanCommonOrderHom n) :=
    cospanBoundaryZeroData_common (A := A) (D := Complex A) (n := n) (sliceOverUncurry b)
  have hobj : ((fiberBoundaryLeftCandidate g h b hb).pullback (cospanCommonOrderHom n)).obj =
      ((fiberBoundaryRightCandidate g h b hb).pullback (cospanCommonOrderHom n)).obj := by
    funext i
    exact cospanBoundaryZeroData_common_obj (A := A) (D := Complex A) (n := n)
      (sliceOverUncurry b) i
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J a c k hJ ha hc hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn,
    SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
  by_cases h0 : J.image (cospanCommonOrderHom n) = cospanPrefixFaces n
  · exact (fiberBoundaryLeftCandidate_prefix_heq g h b hb _ h0 _ _ _ _ _ _ _).trans
      (fiberBoundaryRightCandidate_prefix_heq g h b hb _ h0 _ _ _ _ _ _ _).symm
  · by_cases hD : J.image (cospanCommonOrderHom n) =
        insert (cospanLastTail n) (cospanPrefixFaces n)
    · exact (fiberBoundaryLeftCandidate_last_heq g h b hb _ hD _ _ _ _ _ _ _).trans
        (fiberBoundaryRightCandidate_last_heq g h b hb _ hD _ _ _ _ _ _ _).symm
    · rw [fiberBoundaryLeftCandidate_hom_of_ne g h b hb _ h0 hD,
        fiberBoundaryRightCandidate_hom_of_ne g h b hb _ h0 hD]
      exact SimplexData.hom_heq_of_pullback_eq _ _ (cospanCommonOrderHom n)
        (cospanCommonOrderHom n) hbase J a c k hJ ha hc hk hi.injOn hi.injOn

/-- 概要：左右の実際の dg nerve の単体は共通面へ制限すると等しい。
方針：候補データの共通面の等式を単体の外延性で持ち上げる。
規約：HA Proposition 1.3.1.10。使われ方：join の二セルの押し出しによる貼合せ。 -/
lemma fiberBoundarySimplex_common {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) :
    (fiberBoundaryLeftSimplex g h b hb).pullback (cospanCommonOrderHom n) =
      (fiberBoundaryRightSimplex g h b hb).pullback (cospanCommonOrderHom n) :=
  Simplex.ext (fiberBoundaryCandidate_common g h b hb)

end SerrePositivity.InfinityCategories.DGNerve
