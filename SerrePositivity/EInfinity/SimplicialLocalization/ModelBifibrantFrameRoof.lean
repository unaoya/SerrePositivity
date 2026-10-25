module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantFrameElements
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
def modelBifibrantSourceFrameRoofMap : nerve (modelBifibrantSourceFrameElementCategory X Y q) ⟶
    pullback (sliceOverProjection (SSet.yonedaEquiv.symm
      (nerveVertex (modelBifibrantObject C Y)) ≫
        hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)))
      (nerveMap (modelBifibrantDKFrame X q) ≫
        hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) :=
  (modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom ≫
    frameRoofMap (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))

/-- 概要：元の bifibrant frame の同じ屋根比較と次数射影を回収する。
方針：元の要素圏同型と raw roof の全三角形を合成する。
規約：同じ実比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceFrameRoofMap_degree :
    modelBifibrantSourceFrameRoofMap X Y q ≫ pullback.snd _ _ =
      modelBifibrantSourceFrameElementDegreeNerve X Y q := by
  rw [modelBifibrantSourceFrameRoofMap, Category.assoc, frameRoofMap_degree]
  rfl

/-- 概要：元の bifibrant frame の同じ屋根比較と次数射影を回収する。
方針：元の要素圏同型と raw roof の全三角形を合成する。
規約：同じ実比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceFrameRoofMap_isLeftCofinal_iff_raw :
    IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) ↔
      IsLeftCofinal (rawRoofFunctorMap
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))
        (nerveMap (modelBifibrantDKFrame X q))
        (SSet.yonedaEquiv.symm
          (nerveVertex (modelBifibrantObject C Y)))) := by
  have hi := isLeftCofinal_of_isIso (modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom
  have h : IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) ↔
      IsLeftCofinal (frameRoofMap (modelBifibrantDKFrame X q)
        (modelBifibrantObject C Y)
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))) :=
    ⟨hi.cancel_left, hi.comp⟩
  exact h.trans (frameRoofMap_isLeftCofinal_iff_raw _ _ _)

end SerrePositivity.EInfinity.SimplicialLocalization
