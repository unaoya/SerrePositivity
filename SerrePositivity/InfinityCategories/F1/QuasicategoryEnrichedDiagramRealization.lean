module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramFunctor
public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramRealizationEvaluation

/-!
概要：底全体の quasicategory 値豊穣図式を、元の Hom の core に関する coherent な族へ実現する。
方針：元の図式値豊穣関手を core へ移し、同じ Cat∞ 値の共同評価を合成する。
規約：全変換空間の充填性を要求しない。
使われ方：底変換比較を全 fibration と底の全対象・全射で同時に実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance quasicategoryEnrichedDiagram_sourceCore_simplicialCategory
    {C : Type v} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

/-- 元の全高次の図式への作用を、同じ Hom の core に制限する。 -/
def QuasicategoryEnrichedDiagram.toCoreEnrichedFunctor
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) :
    EnrichedFunctor SSet.{u} (TransportEnrichment quasicategoryCoreFunctor.{u} C)
      (QuasicategoryDiagramCategory J) :=
  quasicategoryCoreEnrichedFunctor D.toEnrichedFunctor

/-- 元の全対象と全高次 Hom の同じ図式を、Cat∞ 値の関手の族へ実現する。 -/
def QuasicategoryEnrichedDiagram.realization
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) :
    SimplicialNerve (TransportEnrichment quasicategoryCoreFunctor.{u} C) ⟶
      CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) :=
  coherentNerveMap D.toCoreEnrichedFunctor ≫ quasicategoryDiagramRealization J

/-- 同じ core の図式の一対象での評価は、元の豊穣関手の同じ core 上の作用。 -/
lemma QuasicategoryEnrichedDiagram.toCoreEnrichedFunctor_evaluate
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) (j : J) :
    D.toCoreEnrichedFunctor.comp SSet (quasicategoryDiagramCoreEvaluationEnriched j) =
      quasicategoryCoreEnrichedFunctor (D.obj j) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 実現した同じ図式の各対象での評価は、元の豊穣関手の同じ coherent nerve。 -/
lemma QuasicategoryEnrichedDiagram.realization_evaluate
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J) (j : J) :
    D.realization ≫ evaluateFunctorAt (ULift.up (nerveVertex j)) =
      coherentNerveMap (quasicategoryCoreEnrichedFunctor (D.obj j)) := by
  rw [realization, Category.assoc, quasicategoryDiagramRealization_evaluate]
  change coherentNerveMap D.toCoreEnrichedFunctor ≫
    coherentNerveMap (quasicategoryDiagramCoreEvaluationEnriched j) = _
  rw [← coherentNerveMap_comp, D.toCoreEnrichedFunctor_evaluate]

end SerrePositivity.InfinityCategories
