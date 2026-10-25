module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofNativeTriangle
public import SerrePositivity.InfinityCategories.Derived.RelativeRoofComparisonCofinality

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
    IsLeftCofinal (rawRoofFunctorMap
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (nerveMap (modelBifibrantDKFrame X q))
      (SSet.yonedaEquiv.symm
        (nerveVertex (modelBifibrantObject C Y)))) :=
  (modelBifibrantSourceFrameRoofMap_isLeftCofinal_iff_raw X Y q).mp
    (modelBifibrantSourceRoofMap_isLeftCofinal X Y q r)

/-- 概要：元の frame の全 roof の余終性を同じ right Kan 次数比較へ戻す。
方針：相対 roof 判定と実 coslice の始対象性を使う。
規約：第一分解と指定 right frame。使われ方：hammock の局所化普遍性。 -/
lemma modelBifibrantFrameRightKanMap_isLeftCofinal :
    IsLeftCofinal (modelBifibrantFrameRightKanMap X q) := by
  apply isLeftCofinal_of_relativeRoofComparisons
  · intro c
    apply (relativeRoofComparison_isLeftCofinal_iff_raw _ _ _ _).mpr
    change IsLeftCofinal (rawRoofFunctorMap
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (modelBifibrantFrameRightKanMap X q ≫ rightKanProjection
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex X))
      (SSet.yonedaEquiv.symm c ≫ rightKanProjection
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex X)))
    rw [modelBifibrantFrameRightKanMap_projection]
    let Y : HomotopicalAlgebra.BifibrantObject C := AsSmall.down.obj (((rightKanProjection
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
      (modelBifibrantHammockVertex X)).app (Opposite.op ⦋0⦌) c).obj 0)
    have hp : SSet.yonedaEquiv.symm c ≫ rightKanProjection
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
        (modelBifibrantHammockVertex X) = SSet.yonedaEquiv.symm
          (nerveVertex (modelBifibrantObject C Y)) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
        SSet.yonedaEquiv.apply_symm_apply]
      exact ComposableArrows.ext₀ rfl
    rw [hp]
    exact modelBifibrantSourceFrameRawRoofMap_isLeftCofinal X q r Y
  · exact FrameHom.FrameArrows.frameRightKanMap_coslice_initial _ _ _ _
  · exact modelFrameIndex_weaklyContractible

end SerrePositivity.EInfinity.SimplicialLocalization
