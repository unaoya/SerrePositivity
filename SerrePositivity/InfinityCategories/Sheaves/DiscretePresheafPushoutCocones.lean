module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscretePushoutCocones
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：集合値前層の指定押し出し余錐を同じ離散前層の余極限として実現する。
方針：元の全余錐の評価を同じ集合の余錐へ照合し、点ごとの余極限判定を使う。
  文献対応：HTT 5.1.2.3・6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）、S8-3。
規約：単射性は一脚だけ。頂点と全ての脚、高次の族を同じ実現で保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C I : Type u} [SmallCategory C] [SmallCategory I]
  {F : I ⥤ (Cᵒᵖ ⥤ Type u)}

/-- 元の集合値前層の全余錐を同じ離散図式の実現で送る。
HTT 5.1.2.3、Kerodon 5.6.0.6（Tag 028T）。構成は余極限性を要求しない。 -/
def discretePresheafCocone (c : Cocone F) :
    JoinCocone (strictCoherentDiagram (F ⋙ kanDiscretePresheafFunctor C) ≫
      kanDiagramRealization Cᵒᵖ) :=
  mapJoinCocone (kanDiagramRealization Cᵒᵖ)
    (strictNativeCocone ((kanDiscretePresheafFunctor C).mapCocone c))

/-- 指定余錐の頂点は元の前層の離散表示そのもの。
HTT 5.1.2.3、Kerodon 5.6.0.6（Tag 028T）、頂点の保持の法則。 -/
lemma discretePresheafCocone_vertex (c : Cocone F) :
    (discretePresheafCocone c).vertex = functorVertex (discretePresheaf c.pt) := by
  rw [discretePresheafCocone,
    SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex,
    strictNativeCocone_vertex, kanDiagramRealization_vertex]
  rfl

/-- 指定した離散前層余錐の全体を評価すると、元の集合の同じ余錐になる。
HTT 5.1.2.3、Kerodon 5.6.0.6（Tag 028T）。頂点だけの比較に弱めない。 -/
lemma discretePresheafCocone_evaluate_val (c : Cocone F) (U : Cᵒᵖ) :
    (mapJoinCocone (evaluateFunctorAt (ULift.up (nerveVertex U)))
      (discretePresheafCocone c)).val =
      (discreteSpaceCocone (((evaluation Cᵒᵖ (Type u)).obj U).mapCocone c)).val := by
  change (strictNativeCocone ((kanDiscretePresheafFunctor C).mapCocone c)).val ≫
      kanDiagramRealization Cᵒᵖ ≫ evaluateFunctorAt (ULift.up (nerveVertex U)) = _
  rw [kanDiagramRealization_evaluate]
  change (strictNativeCocone ((kanDiscretePresheafFunctor C).mapCocone c)).val ≫
      coherentNerveMap (kanDiagramEvaluationEnriched U) = _
  rw [strictNativeCocone_postcomp_val, discreteSpaceCocone,
    coherentCoconeOfDiagramEq_val]
  change (strictNativeCocone ((kanDiscretePresheafFunctor C ⋙
      coherentEnrichedUnderlyingFunctor (kanDiagramEvaluationEnriched U)).mapCocone c)).val =
    (strictNativeCocone ((((evaluation Cᵒᵖ (Type u)).obj U) ⋙ setsToKan).mapCocone c)).val
  rw [kanDiscretePresheafFunctor_evaluation]

/-- 単射を一脚とする前層の押し出し余錐の実現は、同じ前層の無限圏の余極限。
HTT 5.1.2.3・6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）。 -/
lemma discretePresheafCocone_isColimit_of_span_mono
    {F : AsSmall.{u} WalkingSpan ⥤ (Cᵒᵖ ⥤ Type u)}
    (c : Cocone F) (hc : IsColimit c)
    [Mono (F.map (AsSmall.up.map WalkingSpan.Hom.fst))] :
    IsColimitCone (discretePresheafCocone c) := by
  apply isColimitCone_of_pointwise
  rintro ⟨s⟩
  obtain ⟨U, rfl⟩ := ComposableArrows.mk₀_surjective s
  apply (isColimitCone_iff_of_cocone_val_eq _ _
    (discretePresheafCocone_evaluate_val c U)).mpr
  have : Mono ((F ⋙ (evaluation Cᵒᵖ (Type u)).obj U).map
      (AsSmall.up.map WalkingSpan.Hom.fst)) :=
    inferInstanceAs (Mono ((F.map (AsSmall.up.map WalkingSpan.Hom.fst)).app U))
  exact discreteSpaceCocone_isColimit_of_span_mono
    (((evaluation Cᵒᵖ (Type u)).obj U).mapCocone c)
    (isColimitOfPreserves _ hc)

end SerrePositivity.InfinityCategories.Sheaves
