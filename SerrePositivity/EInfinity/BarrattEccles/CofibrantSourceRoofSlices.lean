module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameRoof
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofQuillenSlice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft

/-!
# 元の cofibrant source 屋根の全 Quillen A slice と次数モデル

概要：元の指定点の全 slice を、同じ次数へ向かう Over 図式へ送る。
方針：元の frame 射の反転で標的の左右ファイブレーション性を示し、全射影を保持する。
規約：任意可換環・元の q・元の全単体を使う。slice の弱可縮性は別工程。
使われ方：実屋根比較の left cofinal 性の判定と有限次数モデル。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

abbrev cofibrantSourceRoofTarget := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget (cofibrantDKSourceFrame A X)
  (show (cofibrantAlgebraRelativeCategory A).category from Y)
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))

abbrev cofibrantSourceRoofProjection : cofibrantSourceRoofTarget A X Y ⟶
    nerve (AsSmall.{u + 1} SimplexCategory) := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection _ _ _

lemma cofibrantSourceFrameArrow_invertible {i j : AsSmall.{u + 1} SimplexCategory}
    (f : i ⟶ j) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      ((nerve.edgeMk ((cofibrantDKSourceFrame A X).map f)).map
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))).toTruncated := by
  have hi := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_weak_invertible (cofibrantAlgebraRelativeCategory A)
    ((cofibrantDKSourceFrame A X).map f) (cofibrantDKSourceFrame_map_weak A X f)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (X := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A))
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor (cofibrantAlgebraRelativeCategory A)).map
      ((cofibrantDKSourceFrame A X).map f))).toTruncated)
    (f := ((nerve.edgeMk ((cofibrantDKSourceFrame A X).map f)).map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))).toTruncated)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_arrow (cofibrantAlgebraRelativeCategory A)
      ((cofibrantDKSourceFrame A X).map f)).symm).mp hi

lemma cofibrantSourceRoofProjection_rightFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (cofibrantSourceRoofProjection A X Y) := inferInstance

lemma cofibrantSourceRoofProjection_leftFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (cofibrantSourceRoofProjection A X Y) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection_leftFibration _ _ _ (cofibrantSourceFrameArrow_invertible A X)

lemma cofibrantSourceRoofTarget_quasicategory :
    SSet.Quasicategory (cofibrantSourceRoofTarget A X Y) := inferInstance

variable (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

abbrev cofibrantSourceRoofSlice := pullback (cofibrantSourceFrameRoofMap A X Y)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))

abbrev cofibrantSourceRoofDegree := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree (cofibrantDKSourceFrame A X)
  (show (cofibrantAlgebraRelativeCategory A).category from Y)
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b

def cofibrantSourceRoofSliceOver : cofibrantSourceRoofSlice A X Y b ⟶
    nerve (Over (cofibrantSourceRoofDegree A X Y b)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceOver _ _ _ _ (cofibrantSourceFrameRoofMap A X Y)

lemma cofibrantSourceRoofSliceOver_projection :
    cofibrantSourceRoofSliceOver A X Y b ≫
      nerveMap (Over.forget (cofibrantSourceRoofDegree A X Y b)) =
        pullback.fst _ _ ≫ sourceFrameElementDegreeNerve A X Y := by
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenSliceOver_projection (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b
    (cofibrantSourceFrameRoofMap A X Y)
  change cofibrantSourceRoofSliceOver A X Y b ≫ _ =
    (pullback.fst _ _ ≫ cofibrantSourceFrameRoofMap A X Y) ≫ pullback.snd _ _ at h
  rw [Category.assoc, cofibrantSourceFrameRoofMap_degree] at h
  exact h

abbrev cofibrantSourceRoofDegreeModel := pullback (sourceFrameElementDegreeNerve A X Y)
  (nerveMap (Over.forget (cofibrantSourceRoofDegree A X Y b)))

def cofibrantSourceRoofSliceDegreeMap : cofibrantSourceRoofSlice A X Y b ⟶
    cofibrantSourceRoofDegreeModel A X Y b :=
  pullback.lift (pullback.fst _ _) (cofibrantSourceRoofSliceOver A X Y b)
    (cofibrantSourceRoofSliceOver_projection A X Y b).symm

lemma cofibrantSourceRoofSliceDegreeMap_source : cofibrantSourceRoofSliceDegreeMap A X Y b ≫
    pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

lemma cofibrantSourceRoofMap_isLeftCofinal_iff_slices :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRoofMap A X Y) ↔
      ∀ b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (cofibrantSourceRoofSlice A X Y b) := by
  have := cofibrantSourceRoofTarget_quasicategory A X Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_iff_weaklyContractible_slices _

end SerrePositivity.EInfinity.BarrattEccles
