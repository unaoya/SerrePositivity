module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionBaseChangeCompValueNormalization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValueHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeRealizationComposition

/-!
概要：指定反復引き戻し比較の値を、分類した同じ全空間射へつなぐ。
方針：同じ共同比較の係数値と、相対後合成の実現の法則を照合する。
規約：標準同型の逆射による直接引き戻しから反復引き戻しへの向きを保つ。
使われ方：Kerodon §5.6（Tag 027M）の分類における、指定底変換の貼り合わせ法則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.LimitsAndColimits.LimitsAndColimits
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance sectionCompClassified_pullbackLeft {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：指定した標準比較の実現値は、元の逆引き戻し射の分類の初頂点制限。
方針：同じ全空間射の分類と切断作用の自然性に、指定実現値の計算を適用する。
規約：図式全体の同じHomの可換式。使われ方：指定底変換の三因子の第一因子の照合。 -/
lemma sectionBaseChangeCompComparison_classified_hom {E B D T : SSet.{u}}
    [Quasicategory T] (p : E ⟶ B) [LeftFibration p]
    (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    (show FunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T) ≫
          leftStraighteningInfinityDiagram q₀)
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T) ≫
          leftStraighteningInfinityDiagram q₁) from
      precomposeFunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T))
        (leftClassificationHom q₀ q₁ (pullbackLeftPullbackSndIso p k l).inv
          (pullbackLeftPullbackSndIso_inv_snd_snd p k l))) ≫
      (leftClassificationSimplexIso q₁).hom =
      (show FunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T) ≫
          leftStraighteningInfinityDiagram q₀)
        (kanDiagramCoherentNerve
          ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor T)).evaluate
            (leftFibrationObjectOf q₀))) from (leftClassificationSimplexIso q₀).hom) ≫
        (kanEnrichedRealizationValueIso
          (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
          (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
          (leftFibrationObjectOf p)).hom := by
  dsimp only
  rw [sectionBaseChangeCompComparison_value_hom]
  exact leftClassificationHom_simplexRestriction
    (pullback.snd p (l ≫ k)) (pullback.snd (pullback.snd p k) l)
    (pullbackLeftPullbackSndIso p k l).inv (pullbackLeftPullbackSndIso_inv_snd_snd p k l)

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
