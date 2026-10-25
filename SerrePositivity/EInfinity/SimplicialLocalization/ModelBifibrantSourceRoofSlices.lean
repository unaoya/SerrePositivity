module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantFrameRoof
public import SerrePositivity.EInfinity.FrameHom.FrameRoofQuillenSlice
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenALeft

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
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom.FrameArrows
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofTarget := roofTarget (modelBifibrantDKFrame X q)
  (modelBifibrantObject C Y)
  (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofProjection : modelBifibrantSourceRoofTarget X Y q ⟶
    nerve (AsSmall.{max u v} SimplexCategory) := roofTargetProjection _ _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceFrameArrow_invertible {i j : AsSmall.{max u v} SimplexCategory}
    (f : i ⟶ j) : IsInvertibleEdge
      ((nerve.edgeMk ((modelBifibrantDKFrame X q).map f)).map
        (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))).toTruncated := by
  have hi := kanHammockSourceFunctor_weak_invertible (modelBifibrantRelativeCategory C)
    ((modelBifibrantDKFrame X q).map f) (modelBifibrantDKFrame_map_weak X q f)
  exact (isInvertibleEdge_congr
    (X := kanHammockNerve (modelBifibrantRelativeCategory C))
    (e := (coherentNerveEdge ((kanHammockSourceFunctor (modelBifibrantRelativeCategory C)).map
      ((modelBifibrantDKFrame X q).map f))).toTruncated)
    (f := ((nerve.edgeMk ((modelBifibrantDKFrame X q).map f)).map
      (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C))).toTruncated)
    (hammockLocalizationNerveMap_arrow (modelBifibrantRelativeCategory C)
      ((modelBifibrantDKFrame X q).map f)).symm).mp hi

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProjection_rightFibration :
    RightFibration (modelBifibrantSourceRoofProjection X Y q) := inferInstance

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProjection_leftFibration :
    LeftFibration (modelBifibrantSourceRoofProjection X Y q) :=
  roofTargetProjection_leftFibration _ _ _ (modelBifibrantSourceFrameArrow_invertible X q)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofTarget_quasicategory :
    SSet.Quasicategory (modelBifibrantSourceRoofTarget X Y q) := inferInstance

variable (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofSlice := pullback (modelBifibrantSourceFrameRoofMap X Y q)
  (sliceOverProjection (SSet.yonedaEquiv.symm b))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofDegree := roofTargetDegree (modelBifibrantDKFrame X q)
  (modelBifibrantObject C Y)
  (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofSliceOver : modelBifibrantSourceRoofSlice X Y q b ⟶
    nerve (Over (modelBifibrantSourceRoofDegree X Y q b)) :=
  roofQuillenSliceOver _ _ _ _ (modelBifibrantSourceFrameRoofMap X Y q)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceOver_projection :
    modelBifibrantSourceRoofSliceOver X Y q b ≫
      nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b)) =
        pullback.fst _ _ ≫ modelBifibrantSourceFrameElementDegreeNerve X Y q := by
  have h := roofQuillenSliceOver_projection (modelBifibrantDKFrame X q)
    (modelBifibrantObject C Y)
    (hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b
    (modelBifibrantSourceFrameRoofMap X Y q)
  change modelBifibrantSourceRoofSliceOver X Y q b ≫ _ =
    (pullback.fst _ _ ≫ modelBifibrantSourceFrameRoofMap X Y q) ≫ pullback.snd _ _ at h
  rw [Category.assoc, modelBifibrantSourceFrameRoofMap_degree] at h
  exact h

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofDegreeModel :=
  pullback (modelBifibrantSourceFrameElementDegreeNerve X Y q)
  (nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b)))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofSliceDegreeMap : modelBifibrantSourceRoofSlice X Y q b ⟶
    modelBifibrantSourceRoofDegreeModel X Y q b :=
  pullback.lift (pullback.fst _ _) (modelBifibrantSourceRoofSliceOver X Y q b)
    (modelBifibrantSourceRoofSliceOver_projection X Y q b).symm

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofSliceDegreeMap_source :
  modelBifibrantSourceRoofSliceDegreeMap X Y q b ≫
    pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofMap_isLeftCofinal_iff_slices :
    IsLeftCofinal (modelBifibrantSourceFrameRoofMap X Y q) ↔
      ∀ b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌,
        IsWeaklyContractible (modelBifibrantSourceRoofSlice X Y q b) := by
  have := modelBifibrantSourceRoofTarget_quasicategory X Y q
  exact isLeftCofinal_iff_weaklyContractible_slices _

end SerrePositivity.EInfinity.SimplicialLocalization
