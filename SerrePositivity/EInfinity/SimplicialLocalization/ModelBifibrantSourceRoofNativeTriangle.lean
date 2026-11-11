module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismZero
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismOne
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismFamilyComposition
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofGeometricLeftCell

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNative_triangle
    (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌) :
    (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductCommaNativeIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b := by
  have hl :
      (β_ (nerve (modelBifibrantSourceRoofProductComma X Y q b)) (Δ[1] : SSet.{max u v})).hom ≫
        modelBifibrantSourceRoofProductCommaNativePrism X Y q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b).h := by
    rw [modelBifibrantSourceRoofProductCommaNativePrism_projection X Y q b,
      ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.slicePrismFamily_comp (modelBifibrantHammockVertex Y)
    (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b)
    (modelBifibrantSourceRoofProductCommaRightHomotopy X Y q b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (modelBifibrantSourceRoofProductCommaNativePinchedMap X Y q b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
    (modelBifibrantSourceRoofProductCommaNativePrism X Y q b)
    (modelBifibrantSourceRoofProductCommaNativePrism_zero_evaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaNativePrism_one_evaluation X Y q b) hl
  rw [modelBifibrantSourceRoofProductCommaEvaluationHomotopy_hom X Y q b] at h
  exact h

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductReference_triangle
    (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌) :
    (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductReferenceIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b :=
  (by
    rw [← modelBifibrantSourceRoofProductCommaNativeIntervalCell_eq_reference]
    exact modelBifibrantSourceRoofProductCommaNative_triangle X Y q b)

variable [(HomotopicalAlgebra.cofibrations C).HasFunctorialFactorization
  (HomotopicalAlgebra.trivialFibrations C)]
  (r : SerrePositivity.Reedy.CofibrantResolutionFamily (C := Cᵒᵖ) SerrePositivity.Reedy.simplex)
include r in
/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofMap_isLeftCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) :=
  modelBifibrantSourceRoofMap_isLeftCofinal_of_reference_triangle X Y q r
    (modelBifibrantSourceRoofProductReference_triangle X Y q)

end SerrePositivity.EInfinity.SimplicialLocalization
