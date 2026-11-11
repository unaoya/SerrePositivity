module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofBaseEvaluation
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductFunctorCell

/-!
# 元の標準評価の円柱と Over 終対象円柱の像

概要：元の D_m→D_n の自然変換の円柱を Over の標準終対象円柱から回収する。
方針：元の忘却像と frame による後合成の全円柱の自然性を使う。
規約：元の評価の射と同じ q・同じ指定次数を保つ。
使われ方：実左脚の全関手圏での評価同型との同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open SerrePositivity.EInfinity.FrameHom SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

def cofibrantSourceRoofProductCommaEvaluationHomotopy : SSet.Homotopy
    (nerveMap (cofibrantSourceRoofProductCommaDiagram A X Y b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (SSet.const (X := nerve (cofibrantSourceRoofProductComma A X Y b))
      (cofibrantHammockVertex A (cofibrantSourceRoofDegreeAlgebra A X Y b))) := by
  exact FrameHom.FrameArrows.augmentationHomotopy
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))

lemma cofibrantSourceRoofProductCommaEvaluationHomotopy_h :
    (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (cofibrantSourceRoofProductCommaEvaluation A X Y b)).h ≫
        SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A) := rfl

lemma cofibrantSourceRoofProductCommaEvaluationHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b)) =
        (cofibrantSourceRoofProductCommaEvaluationIso A X Y b).hom := by
  rfl

lemma cofibrantSourceRoofProductOverTerminalHomotopy_evaluation_h :
    (overTerminalHomotopy (cofibrantSourceRoofDegree A X Y b)
      (cofibrantSourceRoofProductCommaOver A X Y b)).h ≫
      nerveMap (Over.forget (cofibrantSourceRoofDegree A X Y b)) ≫
        nerveMap (cofibrantDKSourceFrame A X) ≫
          SimplicialLocalization.hammockLocalizationNerveMap
            (cofibrantAlgebraRelativeCategory A) =
    (cofibrantSourceRoofProductCommaEvaluationHomotopy A X Y b).h := by
  have h : ((cofibrantDKSourceFrame A X).mapCocone
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone (cofibrantSourceRoofDegree A X Y b)).whisker
        (cofibrantSourceRoofProductCommaOver A X Y b))).ι =
      cofibrantSourceRoofProductCommaEvaluation A X Y b := by
    apply NatTrans.ext
    funext s
    rfl
  have hm := overTerminalHomotopy_map_forget_h (cofibrantSourceRoofDegree A X Y b)
    (cofibrantSourceRoofProductCommaOver A X Y b) (cofibrantDKSourceFrame A X)
  rw [h] at hm
  have hpost := congrArg (fun g => g ≫
    SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) hm
  rw [cofibrantSourceRoofProductCommaEvaluationHomotopy_h]
  simpa only [Category.assoc] using hpost

end SerrePositivity.EInfinity.BarrattEccles
