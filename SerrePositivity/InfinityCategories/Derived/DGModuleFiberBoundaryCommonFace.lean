module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryCandidateComponents

/-! # 標準 fiber の左右の充填単体の共通面

概要：左右の明示解を挿入した単体は先頭と D からなる共通面で一致する。
方針：挿入成分は共通の型付き解と比較し、それ以外は零未知基底の一致へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二つの標準セルの貼合せ。
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

/-- 概要：左右の候補データは共通面へ制限すると等しい。
方針：対象を元の共通面から同定し、二つの挿入集合と残りの集合を分けて成分を比較する。
規約：HA Proposition 1.3.1.10。使われ方：左右の単体を貼るための整合条件。 -/
lemma dgModuleFiberBoundaryCandidate_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftCandidate A D f b hb).pullback (cospanCommonOrderHom n) =
      (dgModuleFiberBoundaryRightCandidate A D f b hb).pullback (cospanCommonOrderHom n) := by
  have hi : Function.Injective (cospanCommonOrderHom n) :=
    (cospanFirstTail n).succAboveOrderEmb.injective
  have hbase : (dgModuleFiberBoundaryLeftBase A D f b).pullback (cospanCommonOrderHom n) =
      (dgModuleFiberBoundaryRightBase A D f b).pullback (cospanCommonOrderHom n) :=
    cospanBoundaryZeroData_common (A := A) (D := RightModule A D) (n := n) (sliceOverUncurry b)
  have hobj : ((dgModuleFiberBoundaryLeftCandidate A D f b hb).pullback (cospanCommonOrderHom
    n)).obj =
      ((dgModuleFiberBoundaryRightCandidate A D f b hb).pullback (cospanCommonOrderHom n)).obj := by
    funext i
    exact cospanBoundaryZeroData_common_obj (A := A) (D := RightModule A D) (n := n)
      (sliceOverUncurry b) i
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J a c k hJ ha hc hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn,
    SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
  by_cases h0 : J.image (cospanCommonOrderHom n) = cospanPrefixFaces n
  · exact (dgModuleFiberBoundaryLeftCandidate_prefix_heq A D f b hb _ h0 _ _ _ _ _ _ _).trans
      (dgModuleFiberBoundaryRightCandidate_prefix_heq A D f b hb _ h0 _ _ _ _ _ _ _).symm
  · by_cases hD : J.image (cospanCommonOrderHom n) =
        insert (cospanLastTail n) (cospanPrefixFaces n)
    · exact (dgModuleFiberBoundaryLeftCandidate_last_heq A D f b hb _ hD _ _ _ _ _ _ _).trans
        (dgModuleFiberBoundaryRightCandidate_last_heq A D f b hb _ hD _ _ _ _ _ _ _).symm
    · rw [dgModuleFiberBoundaryLeftCandidate_hom_of_ne A D f b hb _ h0 hD,
        dgModuleFiberBoundaryRightCandidate_hom_of_ne A D f b hb _ h0 hD]
      exact SimplexData.hom_heq_of_pullback_eq _ _ (cospanCommonOrderHom n)
        (cospanCommonOrderHom n) hbase J a c k hJ ha hc hk hi.injOn hi.injOn

/-- 概要：左右の実際の dg nerve の単体は共通面へ制限すると等しい。
方針：候補データの共通面の等式を単体の外延性で持ち上げる。
規約：HA Proposition 1.3.1.10。使われ方：join の二セルの押し出しによる貼合せ。 -/
lemma dgModuleFiberBoundarySimplex_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftSimplex A D f b hb).pullback (cospanCommonOrderHom n) =
      (dgModuleFiberBoundaryRightSimplex A D f b hb).pullback (cospanCommonOrderHom n) :=
  Simplex.ext (dgModuleFiberBoundaryCandidate_common A D f b hb)

end SerrePositivity.InfinityCategories
