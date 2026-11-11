module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullPresheafHomWeightFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafYonedaLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.YonedaWeightLeftKan

/-!
概要：全前層の係数 Hom 族と、指定された Yoneda 左 Kan 延長の全 Hom 族を比較する。
方針：両族を同じ持ち上げた Yoneda の右 Kan 延長として制限の同型から比較する。
規約：元の指定単位を保持し、始域・終域の両変数で全自然な同型を構成する。
使われ方：P-12 の Yoneda 模型を元の関手圏の Hom へ戻すための普遍性入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {A : SSet.{u}} [Quasicategory A]
    {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：前層の元の宇宙変更の全標準 Yoneda 余錐は余極限。
方針：既存の同じ恒等単位付き左 Kan 条件から標準余錐を回収する。
規約：元の宇宙変更を使う。使われ方：全前層 Hom 族の右 Kan 条件。 -/
lemma presheafUniverse_canonicalColimits
    (a : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram A) a) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_canonicalColimits_of_unit_isIso _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafUniverseDiagram_isLeftKanExtension A)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom]
  exact ⟨⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩⟩

/-- 概要：全前層の係数 Hom 族は元の持ち上げた Yoneda の右 Kan 延長。
方針：宇宙変更の標準余錐を全共同 Hom と同じ係数制限へ送る。
規約：全前層と全標的係数を扱う。使われ方：右 Kan の一意性による全自然比較。 -/
lemma fullPresheafHomWeightFamily_isRightKanExtension
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A))))
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homCanonical_isRightKanExtension _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram A)
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀))
    presheafUniverse_canonicalColimits

variable {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D}
    {L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A ≫ L))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) F₀ L β)

/-- 概要：指定左 Kan 延長の全 Hom 族の Yoneda 制限は元の図式の Hom 族と同型。
方針：指定単位の可逆性による回収を持ち上げ、全 co-Yoneda へ写す。
規約：元の指定単位を使う。使われ方：二つの右 Kan 延長の制限比較。 -/
def presheafExtensionHom_restrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily L) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftedHomWeightFamily F₀) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_unit_isIso β hβ
  let r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A ≫ L) F₀ :=
    (asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))).symm
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorIso.ulift.{u + 2, u + 3}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorIso.ulift.{u + 1, u + 2} r).op).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))
  simpa only [Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftedHomWeightFamily] using e

/-- 概要：全前層係数族と指定左 Kan 延長の全 Hom 族は両変数で全自然同型。
方針：元の Yoneda 評価と指定単位で制限を比較し、右 Kan 一意性を適用する。
規約：対象ごとの写像空間同値の存在へ弱めない。
使われ方：全図式に沿う Hom 族の普遍性の移送。 -/
def presheafExtensionHom_liftedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily L) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanReflRestrictionIso _ (fullPresheafHomWeightFamily_isRightKanExtension F₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily_isRightKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) L
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafYonedaLeftKan_canonicalColimits β hβ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily_yonedaRestrictionIso F₀ ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily_evaluationIso F₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homWeightEvaluationFamily_liftedIso F₀ ≪≫
        (presheafExtensionHom_restrictionIso β hβ).symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
