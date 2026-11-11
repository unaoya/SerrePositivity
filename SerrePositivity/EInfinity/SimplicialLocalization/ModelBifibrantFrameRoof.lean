module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelBifibrantFrameElements
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantRightKanShape
public import SerrePositivity.EInfinity.FrameHom.FrameRoofSource

/-!
概要：元の bifibrant source frame の全単体から実 hammock の屋根比較を作る。
方針：同じ要素圏の実同型と元の raw roof 比較を合成する。
規約：元の射と全次数射影を保持する。
使われ方：実 right Kan 次数比較の余終性判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open HomotopicalAlgebra SerrePositivity.Reedy
open SerrePositivity.EInfinity.FrameHom.FrameArrows
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：元の bifibrant frame の同じ屋根比較と次数射影を回収する。
方針：元の要素圏同型と raw roof の全三角形を合成する。
規約：同じ実比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceFrameRoofMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)) ≫
        hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
        hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom ≫
    frameRoofMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))

/-- 概要：元の bifibrant frame の同じ屋根比較と次数射影を回収する。
方針：元の要素圏同型と raw roof の全三角形を合成する。
規約：同じ実比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceFrameRoofMap_degree :
    modelBifibrantSourceFrameRoofMap X Y q ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegreeNerve X Y q := by
  rw [modelBifibrantSourceFrameRoofMap, Category.assoc, frameRoofMap_degree]
  rfl

/-- 概要：元の bifibrant frame の同じ屋根比較と次数射影を回収する。
方針：元の要素圏同型と raw roof の全三角形を合成する。
規約：同じ実比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceFrameRoofMap_isLeftCofinal_iff_raw :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q))
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)))) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (frameRoofMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))) :=
    ⟨hi.cancel_left, hi.comp⟩
  exact h.trans (frameRoofMap_isLeftCofinal_iff_raw _ _ _)

end SerrePositivity.EInfinity.SimplicialLocalization
