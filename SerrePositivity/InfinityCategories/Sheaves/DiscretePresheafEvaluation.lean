module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafInclusion
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpaceCoherentRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage

/-!
概要：離散前層の全埋め込みと対象評価の可換性を全単体で固定する。
方針：Kan 図式の束縛後の豊穣評価と通常 nerve の後合成則を使う。
  文献対応：HTT 5.1.2.3・6.2.2.7、Kerodon Corollary 5.6.0.6（Tag 028T）、S8-3。
規約：重みの射・高次の族も含む射の等式で、対象ごとの同型の選択ではない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 離散図式を束縛した後の評価は、元の集合の評価を離散化する同じ関手。
HTT 5.1.2.3、Kerodon 5.6.0.6（Tag 028T）、評価移送の法則。 -/
lemma kanDiscretePresheafFunctor_evaluation (U : Cᵒᵖ) :
    kanDiscretePresheafFunctor C ⋙
        coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched U) =
      (evaluation Cᵒᵖ (Type u)).obj U ⋙ setsToKan := by
  rw [kanDiscretePresheafFunctor, Functor.assoc, kanDiagramBundle_evaluation]
  rfl

/-- 離散前層の全埋め込みは対象での評価と全単体で可換。
HTT 5.1.2.3・6.2.2.7、Kerodon 5.6.0.6（Tag 028T）。
頂点・辺だけでなく同じ高次の族も保つ。 -/
lemma kanDiscretePresheafMap_evaluate (U : Cᵒᵖ) :
    kanDiscretePresheafMap C ≫ evaluateFunctorAt (ULift.up (nerveVertex U)) =
      nerveMap ((evaluation Cᵒᵖ (Type u)).obj U) ≫ discreteSpaceInclusion := by
  rw [kanDiscretePresheafMap, Category.assoc, Category.assoc,
    kanDiagramRealization_evaluate]
  change nerveMap (kanDiscretePresheafFunctor C) ≫
      (nerveToCoherent (KanDiagramObject Cᵒᵖ) ≫
        coherentNerveMap (kanDiagramEvaluationEnriched U)) = _
  rw [nerveToCoherent_postcomp, ← Category.assoc]
  have hm : nerveMap (kanDiscretePresheafFunctor C ⋙
      coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched U)) =
        nerveMap (kanDiscretePresheafFunctor C) ≫
          nerveMap (coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched U)) :=
    nerveFunctor.map_comp (kanDiscretePresheafFunctor C).toCatHom
      (coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched U)).toCatHom
  rw [← hm, kanDiscretePresheafFunctor_evaluation, discreteSpaceInclusion_eq_coherent,
    ← Category.assoc]
  have hm' : nerveMap ((evaluation Cᵒᵖ (Type u)).obj U ⋙ setsToKan) =
      nerveMap ((evaluation Cᵒᵖ (Type u)).obj U) ≫ nerveMap setsToKan :=
    nerveFunctor.map_comp ((evaluation Cᵒᵖ (Type u)).obj U).toCatHom setsToKan.toCatHom
  rw [hm']

end SerrePositivity.InfinityCategories.Sheaves
