module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramSingletonEvaluation
public import SerrePositivity.InfinityCategories.F1.SubsingletonFunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramRealizationEvaluation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramRealizationComparison
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus

/-!
概要：一点の通常圏の nerve 上で、元の Cat∞ 値分類写像は充満忠実。
方針：同じ strict 変換の成分評価と、分類先の関手評価の厳密な同型を使う。
規約：既存の全相対 Hom の core と元の分類主写像を保つ。
使われ方：同じ Hom 比較の零次元セル上の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C] (c : C)

/-- 一点の底では、元の strict 変換の core の同じ成分評価は同値。 -/
lemma cocartesianTransportDiagramEvaluationEnriched_map_isQCatEquivalence_of_subsingleton
    (F G : CocartesianTransportDiagramCategory C) :
    IsQCatEquivalence ((cocartesianTransportDiagramEvaluationEnriched c).map F G) := by
  haveI : IsIso (strictDiagramMappingComponent F.val G.val c) :=
    strictDiagramMappingComponent_isIso_of_subsingleton F.val G.val c
  letI : Quasicategory (strictDiagramMappingSpace F.val G.val) :=
    cocartesianTransportDiagramObject_sHom_quasicategory F G
  haveI : KanComplex (quasicategoryCoreFunctor.obj (strictDiagramMappingSpace F.val G.val)) :=
    quasicategoryCore_kanComplex _
  letI : Quasicategory (G.val.obj c) :=
    inferInstanceAs (Quasicategory (cocartesianTransportDiagramValue G c).obj)
  haveI : KanComplex (quasicategoryCoreFunctor.obj
      ((ihom (F.val.obj c)).obj (G.val.obj c))) :=
    quasicategoryCore_kanComplex _
  change IsQCatEquivalence
    (quasicategoryCoreFunctor.map (strictDiagramMappingComponent F.val G.val c))
  exact (qCatEquivalenceOfIso (asIso
    (quasicategoryCoreFunctor.map (strictDiagramMappingComponent F.val G.val c)))).isQCatEquivalence

/-- 一点の底上の元の図式の coherent 評価は、同じ全 Hom で充満忠実。 -/
lemma cocartesianTransportDiagramInfinityEvaluation_isFullyFaithful_of_subsingleton :
    IsFullyFaithful (cocartesianTransportDiagramInfinityEvaluation c) := by
  apply (coherentNerveMap_isFullyFaithful_iff
    (cocartesianTransportDiagramEvaluationEnriched c)).mpr
  exact cocartesianTransportDiagramEvaluationEnriched_map_isQCatEquivalence_of_subsingleton c

include c in
/-- 一点の底での元の strict transport の実現写像は充満忠実。 -/
lemma cocartesianTransportDiagramRealization_isFullyFaithful_of_subsingleton :
    IsFullyFaithful (cocartesianTransportDiagramRealization C) := by
  haveI (n : SimplexCategoryᵒᵖ) : Subsingleton ((nerve C).obj n) :=
    nerve_obj_subsingleton_of_subsingletonCategory C n
  haveI (n : SimplexCategoryᵒᵖ) :
      Subsingleton (((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)).obj n) :=
    inferInstanceAs (Subsingleton (ULift.{u + 1} ((nerve C).obj n)))
  have he : IsFullyFaithful (evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (Y := CatInfinity.{u})
      (ULift.up (nerveVertex c))) :=
    (qCatEquivalenceOfIso (subsingletonFunctorEvaluationIso
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) CatInfinity.{u}
        (ULift.up (nerveVertex c)))).isQCatEquivalence.isFullyFaithful
  apply he.cancel_right
  rw [cocartesianTransportDiagramRealization_evaluate]
  exact cocartesianTransportDiagramInfinityEvaluation_isFullyFaithful_of_subsingleton c

include c in
/-- 一点の底上の元の cocartesian fibration の分類主写像そのものは充満忠実。 -/
lemma cocartesianStraighteningCoherentMap_isFullyFaithful_of_subsingleton :
    IsFullyFaithful (cocartesianStraighteningCoherentMap C) := by
  rw [← cocartesianStrictTransportInfinityMap_realization C]
  exact (cocartesianStrictTransportInfinityMap_isFullyFaithful C).comp
    (cocartesianTransportDiagramRealization_isFullyFaithful_of_subsingleton c)

end SerrePositivity.InfinityCategories
