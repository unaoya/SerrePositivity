module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeReindex
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValue

/-!
概要：指定した相対切断の底変換比較の値を、元の大域比較の同じ対象での値へ同定する。
方針：既存の底変換実現の端点正規化を使い、値での同じ端点移送だけを除く。
規約：HTT §3.3.2・Kerodon §5.6（Tag 028T）の構成の特殊な照合。
  源や底の新たな充填性を要求しない。
使われ方：P3-C1PNB、初頂点底変換の具体的な値の照合を大きい定義の展開から切り離す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 指定された底変換の正規化した値は、元の大域比較の同じ値とHEq。 -/
@[cite HTT "3.3.2" (partial := special) "相対切断模型の指定底変換実現の値と元の大域比較の照合。"]
lemma relativeSectionBaseChangeValue_heq :
    ∀ {B D : SSet.{u}} {J : Type u} [Category.{u} J]
      (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (p : LeftFibrationObject B),
    HEq (kanEnrichedRealizationValueIso (relativeSectionBaseChangeComparison k A)
      (relativeSectionBaseChangeComparison_isQCatEquivalence k A) p)
      (functorIsoValue (relativeSectionBaseChangeRealizationIso k A) (coherentNerveVertex p)) := by
  intro B D J instJ k A p
  let K := relativeSectionBaseChangeComparison k A
  let hK := relativeSectionBaseChangeComparison_isQCatEquivalence k A
  have h : HEq (relativeSectionBaseChangeRealizationIso k A) (K.realizationIso hK) :=
    (heq_of_eq (relativeSectionBaseChangeRealizationIso_normalized k A)).trans
      (diagramIsoCongr_heq _ _ _)
  have hv := functorIsoValue_heq_of_heq (relativeSectionBaseChangeRealizationIso k A)
    (K.realizationIso hK)
    ((relativeSectionEnrichedDiagram A).realization_precompose (leftFibrationBaseChangeEnriched k)).symm
    rfl h (coherentNerveVertex p)
  have hc : HEq (kanEnrichedRealizationValueIso K hK p)
      (functorIsoValue (K.realizationIso hK) (coherentNerveVertex p)) := by
    exact iso_endpoints_heq _ _ _
  exact hc.trans hv.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
