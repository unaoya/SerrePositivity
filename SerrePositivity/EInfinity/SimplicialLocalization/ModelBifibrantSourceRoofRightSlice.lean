module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofSourceProjection
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
lemma modelBifibrantSourceFrameRoofMap_normalizedOver :
    modelBifibrantSourceFrameRoofMap X Y q ≫ pullback.fst _ _ ≫
      (roofTargetSlicePointIso (modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C))).hom =
    (modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom ≫
      frameRoofRightSliceMap (modelBifibrantDKFrame X q)
        (modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C)) := by
  have h := frameRoofMap_normalizedOver (modelBifibrantDKFrame X q)
    (modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
  exact (Category.assoc _ _ _).trans (congrArg
    (fun g => (modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom ≫ g) h)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaRightOver : modelBifibrantSourceRoofProductComma X Y q b ⥤
    Over (modelBifibrantObject C Y) :=
  CostructuredArrow.proj _ _ ⋙ modelBifibrantSourceFrameElementsToDK X Y q ⋙
    CostructuredArrow.toOver (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaRightOver_nerve :
    modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
      (modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom ≫
        nerveMap (CostructuredArrow.toOver (modelBifibrantDKFrame X q)
          (modelBifibrantObject C Y)) =
    nerveMap (modelBifibrantSourceRoofProductCommaRightOver X Y q b) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaRightSlice :
    modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫
      roofCornerSourceSliceMap (modelBifibrantDKFrame X q)
        (modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C)) b =
    nerveMap (modelBifibrantSourceRoofProductCommaRightOver X Y q b) ≫
      (SerrePositivity.InfinityCategories.F1B.nerveOverIso
        (modelBifibrantObject C Y)).hom ≫
      sliceOverPostcomp (SSet.yonedaEquiv.symm
        (nerveVertex (modelBifibrantObject C Y)))
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C)) ≫
      (roofTargetSlicePointIso (modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C))).hom := by
  rw [roofCornerSourceSliceMap_eq_source,
    modelBifibrantSourceRoofProductCommaCornerMap_source, Category.assoc,
    modelBifibrantSourceFrameRoofMap_normalizedOver]
  dsimp only [frameRoofRightSliceMap]
  have h := modelBifibrantSourceRoofProductCommaRightOver_nerve X Y q b
  simpa only [Category.assoc] using congrArg
    (fun g => g ≫ (SerrePositivity.InfinityCategories.F1B.nerveOverIso
      (modelBifibrantObject C Y)).hom ≫
      sliceOverPostcomp (SSet.yonedaEquiv.symm
        (nerveVertex (modelBifibrantObject C Y)))
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C)) ≫
      (roofTargetSlicePointIso (modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C))).hom) h

end SerrePositivity.EInfinity.SimplicialLocalization
