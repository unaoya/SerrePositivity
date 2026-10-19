module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryCandidateComponents
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
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 左右の候補は A と後続部分からなる共通面で一致する。 -/
lemma cofiberBoundaryCandidate_common {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).pullback (spanCommonOrderHom n) =
      (cofiberBoundaryRightCandidate f g b hb).pullback (spanCommonOrderHom n) := by
  have hi : Function.Injective (spanCommonOrderHom n) :=
    (spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective
  have hbase := spanBoundaryZeroData_common (A := S) (D := Complex S) (sliceUnderUncurry b)
  have hobj : ((cofiberBoundaryLeftCandidate f g b hb).pullback (spanCommonOrderHom n)).obj =
      ((cofiberBoundaryRightCandidate f g b hb).pullback (spanCommonOrderHom n)).obj := by
    funext i
    exact spanBoundaryZeroData_common_obj (sliceUnderUncurry b) i
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J x y k hJ hx hy hk
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn,
    SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
  by_cases hq : J.image (spanCommonOrderHom n) = spanSuffixFaces n
  · exact (cofiberBoundaryLeftCandidate_suffix_heq_of_eq f g b hb _ hq _ _ _ _ _ _ _).trans
      (cofiberBoundaryRightCandidate_suffix_heq_of_eq f g b hb _ hq _ _ _ _ _ _ _).symm
  · by_cases ha : J.image (spanCommonOrderHom n) = insert 0 (spanSuffixFaces n)
    · exact (cofiberBoundaryLeftCandidate_first_heq_of_eq f g b hb _ ha _ _ _ _ _ _ _).trans
        (cofiberBoundaryRightCandidate_first_heq_of_eq f g b hb _ ha _ _ _ _ _ _ _).symm
    · rw [cofiberBoundaryLeftCandidate_hom_of_ne f g b hb _ _ _ _ _ _ _ _ hq ha,
        cofiberBoundaryRightCandidate_hom_of_ne f g b hb _ _ _ _ _ _ _ _ hq ha]
      exact SimplexData.hom_heq_of_pullback_eq _ _ (spanCommonOrderHom n)
        (spanCommonOrderHom n) hbase J x y k hJ hx hy hk hi.injOn hi.injOn

end SerrePositivity.InfinityCategories
