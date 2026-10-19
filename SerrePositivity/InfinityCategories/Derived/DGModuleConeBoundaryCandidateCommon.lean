module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Derived.SpanCommonRhs
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補データの共通面

概要：左右の Q・A を挿入した候補が A と後続部分からなる共通面で一致する。
方針：二つの挿入成分は共通解で比較し、残りは零未知基底の共通面へ戻す。
規約：HA Proposition 1.3.1.10。使われ方：左右の充填単体の貼合せ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 左右の候補は A と後続部分からなる共通面で一致する。 -/
lemma dgModuleConeBoundaryCandidate_common {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).pullback (spanCommonOrderHom n) =
      (dgModuleConeBoundaryRightCandidate A D f b hb).pullback (spanCommonOrderHom n) := by
  have hi : Function.Injective (spanCommonOrderHom n) :=
    (spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective
  have hbase := spanBoundaryZeroData_common (A := A) (D := RightModule A D) (sliceUnderUncurry b)
  have hobj : ((dgModuleConeBoundaryLeftCandidate A D f b hb).pullback (spanCommonOrderHom n)).obj =
      ((dgModuleConeBoundaryRightCandidate A D f b hb).pullback (spanCommonOrderHom n)).obj := by
    funext i
    exact spanBoundaryZeroData_common_obj (sliceUnderUncurry b) i
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J x y k hJ hx hy hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn,
    SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
  by_cases hq : J.image (spanCommonOrderHom n) = spanSuffixFaces n
  · exact (dgModuleConeBoundaryLeftCandidate_suffix_heq_of_eq A D f b hb _ hq _ _ _ _ _ _ _).trans
      (dgModuleConeBoundaryRightCandidate_suffix_heq_of_eq A D f b hb _ hq _ _ _ _ _ _ _).symm
  · by_cases ha : J.image (spanCommonOrderHom n) = insert 0 (spanSuffixFaces n)
    · exact (dgModuleConeBoundaryLeftCandidate_first_heq_of_eq A D f b hb _ ha _ _ _ _ _ _ _).trans
        (dgModuleConeBoundaryRightCandidate_first_heq_of_eq A D f b hb _ ha _ _ _ _ _ _ _).symm
    · rw [dgModuleConeBoundaryLeftCandidate_hom_of_ne A D f b hb _ _ _ _ _ _ _ _ hq ha,
        dgModuleConeBoundaryRightCandidate_hom_of_ne A D f b hb _ _ _ _ _ _ _ _ hq ha]
      exact SimplexData.hom_heq_of_pullback_eq _ _ (spanCommonOrderHom n)
        (spanCommonOrderHom n) hbase J x y k hJ hx hy hk hi.injOn hi.injOn

end SerrePositivity.InfinityCategories
