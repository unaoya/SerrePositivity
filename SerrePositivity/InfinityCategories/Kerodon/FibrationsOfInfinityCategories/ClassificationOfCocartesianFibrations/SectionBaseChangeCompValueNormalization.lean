module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionBaseChangeCompValueHom

/-!
概要：反復引き戻し比較の元の実現値を、同じ共同比較の正規化した値へ移す。
方針：同じ実現同型の端点移送と、指定点での評価の法則だけを使う。
規約：比較同型を選び直さない。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.LimitsAndColimits.LimitsAndColimits
open Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：指定反復引き戻し実現同型の値は、同じ共同比較の実現値と端点移送だけ異なる。
方針：元の実現前合成の表示を評価し、指定図式への頂点移送を消去する。
規約：任意の添字図式と元の同型を保つ。使われ方：元の標準比較射の分類への接続。 -/
lemma sectionBaseChangeCompRealizationIso_value_heq {E B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (p : E ⟶ B) [LeftFibration p]
    (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    HEq (functorIsoValue (sectionBaseChangeCompRealizationIso k l A)
        (leftFibrationInfinityVertex p))
      (kanEnrichedRealizationValueIso (sectionBaseChangeCompComparison k l A)
        (sectionBaseChangeCompComparison_isQCatEquivalence k l A) (leftFibrationObjectOf p)) := by
  let η := sectionBaseChangeCompComparison k l A
  let hη := sectionBaseChangeCompComparison_isQCatEquivalence k l A
  let R := relativeSectionEnrichedDiagram A
  have hd := R.realization_precompose (leftFibrationBaseChangeEnriched (l ≫ k))
  have he := sectionBaseChangeIteratedRealization k l A
  have hraw := diagramIsoCongr_heq hd he (η.realizationIso hη)
  have hv := functorIsoValue_heq_of_heq
    (sectionBaseChangeCompRealizationIso k l A) (η.realizationIso hη)
    hd.symm he.symm hraw (leftFibrationInfinityVertex p)
  have hn : HEq (kanEnrichedRealizationValueIso η hη (leftFibrationObjectOf p))
      (functorIsoValue (η.realizationIso hη) (leftFibrationInfinityVertex p)) :=
    iso_endpoints_heq (functorIsoValue (η.realizationIso hη) (leftFibrationInfinityVertex p))
      (congrArg HomotopyCategory.mk
        ((R.precompose (leftFibrationBaseChangeEnriched (l ≫ k))).realization_vertex
          (leftFibrationObjectOf p)))
      (congrArg HomotopyCategory.mk
        ((R.precompose ((leftFibrationBaseChangeEnriched k).comp SSet
          (leftFibrationBaseChangeEnriched l))).realization_vertex (leftFibrationObjectOf p)))
  exact hv.trans hn.symm

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
