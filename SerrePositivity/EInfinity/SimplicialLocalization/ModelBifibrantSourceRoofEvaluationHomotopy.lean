module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofBaseEvaluation
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell

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
open SerrePositivity.EInfinity.FrameHom SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaEvaluationHomotopy : SSet.Homotopy
    (nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))) := by
  exact FrameHom.FrameArrows.augmentationHomotopy
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaEvaluationHomotopy_h :
    (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
        (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)).h ≫
        SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) := rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaEvaluationHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b)) =
        (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom := by
  rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductOverTerminalHomotopy_evaluation_h :
    (overTerminalHomotopy (modelBifibrantSourceRoofDegree X Y q b)
      (modelBifibrantSourceRoofProductCommaOver X Y q b)).h ≫
      nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b)) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
          SimplicialLocalization.hammockLocalizationNerveMap
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) =
    (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b).h := by
  have h : ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q).mapCocone
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone
        (modelBifibrantSourceRoofDegree X Y q b)).whisker
        (modelBifibrantSourceRoofProductCommaOver X Y q b))).ι =
      modelBifibrantSourceRoofProductCommaEvaluation X Y q b := by
    apply NatTrans.ext
    funext s
    rfl
  have hm := overTerminalHomotopy_map_forget_h (modelBifibrantSourceRoofDegree X Y q b)
    (modelBifibrantSourceRoofProductCommaOver X Y q b) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
  rw [h] at hm
  have hpost := congrArg (fun g => g ≫
    SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) hm
  rw [modelBifibrantSourceRoofProductCommaEvaluationHomotopy_h]
  simpa only [Category.assoc] using hpost

end SerrePositivity.EInfinity.SimplicialLocalization
