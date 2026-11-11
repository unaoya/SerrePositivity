module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePrismZero
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePrismOne
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePrismProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismFamilyComposition

/-!
# 元の native roof 全三角形と実屋根の cofinal 性

概要：同じ実 qY slice prism の両端と底から元の全関手圏の三角形を得る。
方針：完成した hb・ht・底円柱を実 slice prism の合成定理へ渡す。
規約：任意可換環・元の実屋根写像・元の基準射を保持する。
使われ方：実右 Kan 比較から元の局所化の普遍性へ進むための屋根比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

lemma cofibrantSourceRoofProductCommaNative_triangle
    (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌) :
    (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductCommaNativeIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b := by
  have hl :
      (β_ (nerve (cofibrantSourceRoofProductComma A X Y b)) (Δ[1] : SSet.{u + 1})).hom ≫
        cofibrantSourceRoofProductCommaNativePrism A X Y b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b).h := by
    rw [cofibrantSourceRoofProductCommaNativePrism_projection A X Y b,
      ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.slicePrismFamily_comp (cofibrantHammockVertex A Y)
    (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b)
    (cofibrantSourceRoofProductCommaRightHomotopy A X Y b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (cofibrantSourceRoofProductCommaNativePinchedMap A X Y b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
    (cofibrantSourceRoofProductCommaNativePrism A X Y b)
    (cofibrantSourceRoofProductCommaNativePrism_zero_evaluation A X Y b)
    (cofibrantSourceRoofProductCommaNativePrism_one_evaluation A X Y b) hl
  rw [cofibrantSourceRoofProductCommaEvaluationHomotopy_hom A X Y b] at h
  exact h

lemma cofibrantSourceRoofProductReference_triangle
    (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌) :
    (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductReferenceIntervalCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b :=
  cofibrantSourceRoofProductReference_triangle_of_native_triangle A X Y b
    (cofibrantSourceRoofProductCommaNative_triangle A X Y b)

lemma cofibrantSourceRoofMap_isLeftCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) :=
  cofibrantSourceRoofMap_isLeftCofinal_of_native_triangles A X Y
    (cofibrantSourceRoofProductCommaNative_triangle A X Y)

end SerrePositivity.EInfinity.BarrattEccles
