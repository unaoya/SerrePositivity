module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativeTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RelativeRoofComparisonCofinality

/-!
# 元の source frame 次数比較の実右 Kan cofinal 性

概要：元の実屋根の cofinal 性から同じ次数比較の left cofinal 性を得る。
方針：全 Quillen A slice を元の実屋根へ戻し、全 coslice 値の始対象性を使う。
規約：全矢図式へ置き換えず、元の次数比較を保持する。
使われ方：局所右 Kan 極限と標準右 Kan 錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : CofibrantAlgebra A)

lemma cofibrantSourceFrameRawRoofMap_isLeftCofinal (Y : CofibrantAlgebra A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
      (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (nerveMap (cofibrantDKSourceFrame A X))
      (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from Y)))) :=
  (cofibrantSourceFrameRoofMap_isLeftCofinal_iff_raw A X Y).mp
    (cofibrantSourceRoofMap_isLeftCofinal A X Y)

lemma cofibrantSourceFrameRightKanMap_isLeftCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (cofibrantSourceFrameRightKanMap A X) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isLeftCofinal_of_relativeRoofComparisons
  · intro c
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison_isLeftCofinal_iff_raw _ _ _ _).mpr
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
      (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (cofibrantSourceFrameRightKanMap A X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (cofibrantHammockVertex A X))
      (SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (cofibrantHammockVertex A X)))
    rw [cofibrantSourceFrameRightKanMap_projection]
    let Y : CofibrantAlgebra A := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
      (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (cofibrantHammockVertex A X)).app (Opposite.op ⦋0⦌) c).obj 0
    have hp : SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
        (cofibrantHammockVertex A X) = SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from Y)) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
        SSet.yonedaEquiv.apply_symm_apply]
      exact ComposableArrows.ext₀ rfl
    rw [hp]
    exact cofibrantSourceFrameRawRoofMap_isLeftCofinal A X Y
  · exact cofibrantSourceFrameRightKanMap_initial A X
  · exact sourceFrameIndex_weaklyContractible.{u}

end SerrePositivity.EInfinity.BarrattEccles
