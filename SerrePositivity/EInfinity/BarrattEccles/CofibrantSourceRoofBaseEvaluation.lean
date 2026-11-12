module

public import SerrePositivity.EInfinity.FrameHom.OverTerminalEvaluation
public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerLeftBase
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofCornerOver
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductGeometricTriangle

/-!
# 実 comma 評価の底円柱は全関手圏で標準終対象円柱に等しい

概要：元の comma 全図式から Over n 上の底円柱を作り、唯一の終対象射へ同定する。
方針：正規化された底の厳密な射影と全関手圏の終対象性を接続する。
規約：任意可換環・元の全パラメータ・選択済み評価を保持する。
使われ方：同じ q の後合成による実左脚と標準評価の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.EInfinity.FrameHom SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom.FrameArrows
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

abbrev cofibrantSourceRoofProductCommaOver :=
  CostructuredArrow.toOver (sourceFrameElementDegree A X Y) (cofibrantSourceRoofDegree A X Y b)

def cofibrantSourceRoofProductNormalizedMap : nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
    roofCornerNormalized (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b :=
  cofibrantSourceRoofProductCommaCornerMap A X Y b ≫
    roofCornerNormalizationMap (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b

lemma cofibrantSourceRoofProductNormalizedMap_over :
    cofibrantSourceRoofProductNormalizedMap A X Y b ≫
      roofCornerNormalizedProjection (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b =
    nerveMap (cofibrantSourceRoofProductCommaOver A X Y b) := by
  simpa only [cofibrantSourceRoofProductNormalizedMap, Category.assoc] using
    cofibrantSourceRoofProductCommaCornerMap_normalizedOver A X Y b

def cofibrantSourceRoofProductBaseHomotopy : SSet.Homotopy
    (nerveMap (cofibrantSourceRoofProductCommaOver A X Y b))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk (𝟙 (cofibrantSourceRoofDegree A X Y b))))) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (terminalFiberBaseHomotopy
    (roofCornerNormalizedProjection (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b)
    _ (roofCornerTerminalEvaluation (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b)
    (cofibrantSourceRoofProductNormalizedMap A X Y b))
    (cofibrantSourceRoofProductNormalizedMap_over A X Y b) rfl

lemma cofibrantSourceRoofProductBaseHomotopy_hom_eq :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (cofibrantSourceRoofProductBaseHomotopy A X Y b)) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (overTerminalHomotopy (cofibrantSourceRoofDegree A X Y b)
        (cofibrantSourceRoofProductCommaOver A X Y b))) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact terminalFiberBaseHomotopy_hom_eq_retarget _ _ _ _
    (roofCornerTerminal_isTerminal (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b)
    _ (cofibrantSourceRoofProductNormalizedMap_over A X Y b) _

lemma cofibrantSourceRoofProductGeometricLeftHomotopy_h_base :
    (cofibrantSourceRoofProductGeometricLeftHomotopy A X Y b).h =
      (cofibrantSourceRoofProductBaseHomotopy A X Y b).h ≫
        nerveMap (Over.forget (cofibrantSourceRoofDegree A X Y b)) ≫
          nerveMap (cofibrantDKSourceFrame A X) ≫
            SimplicialLocalization.hammockLocalizationNerveMap
              (cofibrantAlgebraRelativeCategory A) := by
  have := cofibrantSourceRoofProjection_leftFibration A X Y
  exact roofCornerEvaluationLeftHomotopy_h_base (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) b
    (cofibrantSourceRoofProductCommaCornerMap A X Y b)

end SerrePositivity.EInfinity.BarrattEccles
