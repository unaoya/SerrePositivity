module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerBaseProjection
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection

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
lemma modelBifibrantSourceRoofDegreeTransportIso_inv_over :
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).inv ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]
  exact (modelBifibrantSourceRoofDegreeTransportIso_over X Y q b).symm

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCornerMap_normalizedOver :
    modelBifibrantSourceRoofProductCornerMap X Y q b ≫
      roofCornerNormalizationMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b ≫
      roofCornerNormalizedProjection (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b =
    modelBifibrantSourceRoofProductOverNerve X Y q b := by
  have h := roofQuillenDegreeCornerMap_normalizedOver (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    b (modelBifibrantSourceFrameRoofMap X Y q)
  simp only [modelBifibrantSourceRoofProductCornerMap, Category.assoc, h]
  exact (congrArg (fun g => (modelBifibrantSourceRoofProductIso X Y q b).hom ≫ g)
    (modelBifibrantSourceRoofDegreeTransportIso_inv_over X Y q b)).trans
      (modelBifibrantSourceRoofProductIso_over X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaCornerMap_normalizedOver :
    modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫
      roofCornerNormalizationMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b ≫
      roofCornerNormalizedProjection (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) b =
    nerveMap (CostructuredArrow.toOver (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q)
      (modelBifibrantSourceRoofDegree X Y q b)) := by
  have h : (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      modelBifibrantSourceRoofProductOverNerve X Y q b =
    nerveMap (CostructuredArrow.toOver (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q)
      (modelBifibrantSourceRoofDegree X Y q b)) := by
    rw [Iso.inv_comp_eq]
    exact (modelBifibrantSourceRoofProductCommaIso_over X Y q b).symm
  rw [modelBifibrantSourceRoofProductCommaCornerMap, Category.assoc,
    modelBifibrantSourceRoofProductCornerMap_normalizedOver]
  exact h

end SerrePositivity.EInfinity.SimplicialLocalization
