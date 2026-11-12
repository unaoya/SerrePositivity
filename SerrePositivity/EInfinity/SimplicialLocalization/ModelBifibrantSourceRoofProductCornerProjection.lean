module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerProjectionLaws
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCone
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSliceCriterion

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
open CategoryTheory Limits Opposite SSet
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofDegreeTransportIso_inv_source :
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  exact (modelBifibrantSourceRoofDegreeTransportIso_source X Y q b).symm

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCornerMap_source :
    modelBifibrantSourceRoofProductCornerMap X Y q b ≫ pullback.snd _ _ =
      modelBifibrantSourceRoofProductFirstNerve X Y q b ≫
        modelBifibrantSourceFrameRoofMap X Y q := by
  have h := roofQuillenDegreeCornerMap_source (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    b (modelBifibrantSourceFrameRoofMap X Y q)
  simp only [modelBifibrantSourceRoofProductCornerMap, Category.assoc, h]
  have h₁ := modelBifibrantSourceRoofDegreeTransportIso_inv_source X Y q b
  have h₂ := modelBifibrantSourceRoofProductIso_source X Y q b
  exact (congrArg (fun g => (modelBifibrantSourceRoofProductIso X Y q b).hom ≫ g ≫
    modelBifibrantSourceFrameRoofMap X Y q) h₁).trans
      ((Category.assoc _ _ _).symm.trans (congrArg
        (fun g => g ≫ modelBifibrantSourceFrameRoofMap X Y q) h₂))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaCornerMap :
    nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (modelBifibrantSourceRoofProjection X Y q) :=
  (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
    modelBifibrantSourceRoofProductCornerMap X Y q b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaCornerMap_source :
    modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫ pullback.snd _ _ =
      modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
        modelBifibrantSourceFrameRoofMap X Y q := by
  have h : (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      modelBifibrantSourceRoofProductFirstNerve X Y q b =
        modelBifibrantSourceRoofProductCommaFirstNerve X Y q b := by
    rw [Iso.inv_comp_eq]
    exact (modelBifibrantSourceRoofProductCommaIso_first X Y q b).symm
  rw [modelBifibrantSourceRoofProductCommaCornerMap, Category.assoc,
    modelBifibrantSourceRoofProductCornerMap_source, ← Category.assoc, h]

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaCornerMap_diagram :
    (modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫
      roofCornerSourceSliceMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (modelBifibrantHammockVertex Y)) =
        nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
          SimplicialLocalization.hammockLocalizationNerveMap
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) := by
  have h := roofCornerSourceSliceMap_projection (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b
  have h₁ := modelBifibrantSourceRoofProductCommaCornerMap_source X Y q b
  have h₂ := modelBifibrantSourceFrameRoofMap_degree X Y q
  dsimp only [modelBifibrantHammockVertex]
  calc
    _ = modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫
        (pullback.snd _ _ ≫ modelBifibrantSourceRoofProjection X Y q ≫
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))) :=
      (Category.assoc _ _ _).trans (congrArg
        (fun g => modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫ g) h)
    _ = (modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
        modelBifibrantSourceFrameRoofMap X Y q) ≫ modelBifibrantSourceRoofProjection X Y q ≫
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ modelBifibrantSourceRoofProjection X Y q ≫
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))) h₁
    _ = modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
        _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegreeNerve X Y q ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
          SimplicialLocalization.hammockLocalizationNerveMap
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) := by
      simpa only [Category.assoc] using congrArg
        (fun g => modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫ g ≫
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))) h₂
    _ = _ := by
      simp only [← Category.assoc]
      apply congrArg (fun g => g ≫ SimplicialLocalization.hammockLocalizationNerveMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl

end SerrePositivity.EInfinity.SimplicialLocalization
