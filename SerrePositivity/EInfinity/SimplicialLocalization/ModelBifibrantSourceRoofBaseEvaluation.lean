module

public import SerrePositivity.EInfinity.FrameHom.OverTerminalEvaluation
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerLeftBase
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofCornerOver
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductGeometricTriangle

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
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.EInfinity.FrameHom SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom.FrameArrows
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofProductCommaOver :=
  CostructuredArrow.toOver (modelBifibrantSourceFrameElementDegree X Y q)
    (modelBifibrantSourceRoofDegree X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductNormalizedMap :
  nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    roofCornerNormalized (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b :=
  modelBifibrantSourceRoofProductCommaCornerMap X Y q b ≫
    roofCornerNormalizationMap (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductNormalizedMap_over :
    modelBifibrantSourceRoofProductNormalizedMap X Y q b ≫
      roofCornerNormalizedProjection (modelBifibrantDKFrame X q)
        (modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelBifibrantRelativeCategory C)) b =
    nerveMap (modelBifibrantSourceRoofProductCommaOver X Y q b) := by
  simpa only [modelBifibrantSourceRoofProductNormalizedMap, Category.assoc] using
    modelBifibrantSourceRoofProductCommaCornerMap_normalizedOver X Y q b

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductBaseHomotopy : SSet.Homotopy
    (nerveMap (modelBifibrantSourceRoofProductCommaOver X Y q b))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (nerveVertex (Over.mk (𝟙 (modelBifibrantSourceRoofDegree X Y q b))))) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact stableHomotopyRetarget (terminalFiberBaseHomotopy
    (roofCornerNormalizedProjection (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b)
    _ (roofCornerTerminalEvaluation (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b)
    (modelBifibrantSourceRoofProductNormalizedMap X Y q b))
    (modelBifibrantSourceRoofProductNormalizedMap_over X Y q b) rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductBaseHomotopy_hom_eq :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (modelBifibrantSourceRoofProductBaseHomotopy X Y q b)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (overTerminalHomotopy (modelBifibrantSourceRoofDegree X Y q b)
        (modelBifibrantSourceRoofProductCommaOver X Y q b))) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact terminalFiberBaseHomotopy_hom_eq_retarget _ _ _ _
    (roofCornerTerminal_isTerminal (modelBifibrantDKFrame X q)
      (modelBifibrantObject C Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b)
    _ (modelBifibrantSourceRoofProductNormalizedMap_over X Y q b) _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductGeometricLeftHomotopy_h_base :
    (modelBifibrantSourceRoofProductGeometricLeftHomotopy X Y q b).h =
      (modelBifibrantSourceRoofProductBaseHomotopy X Y q b).h ≫
        nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b)) ≫
          nerveMap (modelBifibrantDKFrame X q) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (modelBifibrantRelativeCategory C) := by
  have := modelBifibrantSourceRoofProjection_leftFibration X Y q
  exact roofCornerEvaluationLeftHomotopy_h_base (modelBifibrantDKFrame X q)
    (modelBifibrantObject C Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (modelBifibrantRelativeCategory C)) b
    (modelBifibrantSourceRoofProductCommaCornerMap X Y q b)

end SerrePositivity.EInfinity.SimplicialLocalization
