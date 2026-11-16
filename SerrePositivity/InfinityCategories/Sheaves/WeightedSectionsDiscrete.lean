module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalLeftLimit
public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf

/-!
概要：元の全重み切断の離散重みでの値を、元の圏上の指定した sectionsOf の値と比較する。
方針：既存の元の圏の同値な比較と同じ底の射影の等式を、指定極限の一意性へ渡す。
規約：元の離散前層の埋め込み、全切断関手、sectionsOf の同じ選択を保持する。
使われ方：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）、S8-4 の集合重みの値。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 離散重みでの同じ全切断関手の値と、元の圏上の指定切断の値の比較。
HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）。指定した元の二つの極限錐の一意性を使う。 -/
def weightedSections_discrete (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : Cᵒᵖ ⥤ Type u) (hP : HasLimit (sectionsOfDiagram P O)) :
    VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm
      ((discretePresheafInclusion C).val.app _ (nerveVertex P)))) (sectionsOf P O hP) := by
  rw [(discretePresheafInclusion C).property.1 P]
  have hd : HasLimit ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O) := hE.hasLimit _
  let d := Classical.choose hd
  have hd' := Classical.choose_spec hd
  let ew := weightedSections_originalLeftLimitIso O hE (discretePresheaf P) d hd'
  have ha : IsQCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural P)) :=
    IsQCatEquivalence.ulift.{u, u + 1}
      (SetWeight.elementsComparisonNatural_isPrecompositionEquivalence P).isQCatEquivalence
  have hp : (SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural P) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallLeftUnstraighteningProjection (discretePresheaf P)) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π P)) := by
    rw [← Functor.map_comp]
    exact congrArg ((SSet.uliftFunctor.{u + 1, u}).map) (SetWeight.elementsComparisonNatural_projection P)
  let es := limitVertexIsoOfOverEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.elementsComparisonNatural P)) ha hp O
    (sectionsOfCone P O hP) d (sectionsOfCone_isLimit P O hP) hd'
  exact ew ≪≫ es.symm

end SerrePositivity.InfinityCategories.Sheaves
