module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundary

/-!
概要：相対 slice 関手空間から、底と終点を共に固定した全余錐の実 fiber への全射。
方針：普遍 uncurry 族の二つの固定境界を curry して実 fiber へ持ち上げる。
規約：全パラメーターで両固定条件を保持。使われ方：相対同型の全余錐への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)

/-- 普遍族の底の curry は、同じ元の図式に厳密に定値。 -/
lemma relativeSliceCoconeCurry_old : curry (relativeSliceCoconeUncurry p b) ≫
    (pre (joinInl A (Δ[0] : SSet.{u}))).app X = SSet.const (functorVertex b) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, relativeSliceCoconeUncurry_old,
    uncurry_const_functorVertex]

/-- 普遍族の頂点の curry も、同じ元の指定点写像に厳密に定値。 -/
lemma relativeSliceCoconeCurry_tip : curry (relativeSliceCoconeUncurry p b) ≫
    (pre (joinInr A (Δ[0] : SSet.{u}))).app X = SSet.const (functorVertex p) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, relativeSliceCoconeUncurry_tip,
    uncurry_const_functorVertex]

/-- 同じ底と終点を固定した全余錐の fiber への、普遍族の実際の全射。 -/
def relativeSliceCoconeBoundaryMap : relativeFunctorSpace (sliceOverProjection p) b ⟶
    fixedCoconeBoundary p b :=
  vertexFiberLift _ _ (curry (relativeSliceCoconeUncurry p b)) (by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, coconeBoundaryPairRestriction, lift_fst, SSet.const_comp]
      exact relativeSliceCoconeCurry_old p b
    · rw [Category.assoc, coconeBoundaryPairRestriction, lift_snd, SSet.const_comp]
      exact relativeSliceCoconeCurry_tip p b)

/-- 同じ fiber の射を含めると、元の普遍全余錐の curry そのもの。 -/
lemma relativeSliceCoconeBoundaryMap_ι : relativeSliceCoconeBoundaryMap p b ≫
    vertexFiberι (coconeBoundaryPairRestriction A X) (functorVertex b, functorVertex p) =
      curry (relativeSliceCoconeUncurry p b) := vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
