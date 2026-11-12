module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductCone
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofCornerEvaluation
public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits

/-!
# 元の積単体の全関手圏内の逆左脚と右脚の合成

概要：元の D_m→D_n の全自然変換を一つの関手同型にして、同じ右脚と合成する。
方針：全成分の反転性で逆を作り、全関手圏の同じ合成関係と実円柱を保持する。
規約：指定 n・元の代数射・全パラメータを保つ。実評価との照合は別工程。
使われ方：実 ProductHomMap と弱な基準射の共通値の高次比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.EInfinity.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCommaEvaluationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))) :=
  augmentationFunctorIso (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (fun s => cofibrantSourceFrameArrow_invertible A X s.hom)

def cofibrantSourceRoofProductCommaRightHomotopy : SSet.Homotopy
    (nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const, SSet.const_comp, cofibrantHammockVertex] using
    HomotopyClasses.postHomotopy
      (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (cofibrantSourceRoofProductCommaRightLeg A X Y b))

def cofibrantSourceRoofProductCommaRightCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (cofibrantSourceRoofProductCommaRightHomotopy A X Y b))

def cofibrantSourceRoofProductCommaComparisonCell : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b)))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) :=
  (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).inv ≫
    cofibrantSourceRoofProductCommaRightCell A X Y b

lemma cofibrantSourceRoofProductCommaComparisonCell_triangle :
    (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫
      cofibrantSourceRoofProductCommaComparisonCell A X Y b =
        cofibrantSourceRoofProductCommaRightCell A X Y b := by
  rw [cofibrantSourceRoofProductCommaComparisonCell, Iso.hom_inv_id_assoc]

lemma cofibrantSourceRoofProductCommaComparisonCell_unique
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
        (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b)))
      (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
        (cofibrantHammockVertex A Y)))
    (h : (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom ≫ c =
      cofibrantSourceRoofProductCommaRightCell A X Y b) :
    c = cofibrantSourceRoofProductCommaComparisonCell A X Y b := by
  apply (cancel_epi (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom).1
  exact h.trans (cofibrantSourceRoofProductCommaComparisonCell_triangle A X Y b).symm

def cofibrantSourceRoofProductCommaComparisonHomotopy : SSet.Homotopy
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b)))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (cofibrantSourceRoofProductCommaComparisonCell A X Y b)

lemma cofibrantSourceRoofProductCommaComparisonHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (cofibrantSourceRoofProductCommaComparisonHomotopy A X Y b)) =
        cofibrantSourceRoofProductCommaComparisonCell A X Y b := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _

end SerrePositivity.EInfinity.BarrattEccles
