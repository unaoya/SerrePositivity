module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeTriangle
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
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Limits SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [(HomotopicalAlgebra.cofibrations C).HasFunctorialFactorization
    (HomotopicalAlgebra.trivialFibrations C)]
  (X : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (r : SerrePositivity.Reedy.CofibrantResolutionFamily (C := Cᵒᵖ) SerrePositivity.Reedy.simplex)
include r

/-- 概要：元の frame の全 roof の余終性を同じ right Kan 次数比較へ戻す。
方針：相対 roof 判定と実 coslice の始対象性を使う。
規約：第一分解と指定 right frame。使われ方：hammock の局所化普遍性。 -/
lemma modelBifibrantSourceFrameRawRoofMap_isLeftCofinal (Y : HomotopicalAlgebra.BifibrantObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q))
      (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)))) :=
  (modelBifibrantSourceFrameRoofMap_isLeftCofinal_iff_raw X Y q).mp
    (modelBifibrantSourceRoofMap_isLeftCofinal X Y q r)

/-- 概要：元の frame の全 roof の余終性を同じ right Kan 次数比較へ戻す。
方針：相対 roof 判定と実 coslice の始対象性を使う。
規約：第一分解と指定 right frame。使われ方：hammock の局所化普遍性。 -/
lemma modelBifibrantFrameRightKanMap_isLeftCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantFrameRightKanMap X q) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isLeftCofinal_of_relativeRoofComparisons
  · intro c
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison_isLeftCofinal_iff_raw _ _ _ _).mpr
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (modelBifibrantFrameRightKanMap X q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex X))
      (SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex X)))
    rw [modelBifibrantFrameRightKanMap_projection]
    let Y : HomotopicalAlgebra.BifibrantObject C := AsSmall.down.obj (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (modelBifibrantHammockVertex X)).app (Opposite.op ⦋0⦌) c).obj 0)
    have hp : SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex X) = SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
        SSet.yonedaEquiv.apply_symm_apply]
      exact ComposableArrows.ext₀ rfl
    rw [hp]
    exact modelBifibrantSourceFrameRawRoofMap_isLeftCofinal X q r Y
  · exact FrameHom.FrameArrows.frameRightKanMap_coslice_initial _ _ _ _
  · exact modelFrameIndex_weaklyContractible

end SerrePositivity.EInfinity.SimplicialLocalization
