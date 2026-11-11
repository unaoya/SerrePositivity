module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyOriginalSuspension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CosliceTransport

/-! # 元の点つき射と suspension の coherent な図式
概要：Kan 包含と suspension の豊穣作用を、元の通常の対象・射・図式と照合する。
方針：写像空間の頂点で通常の作用を回収し、strict な図式の後合成を使う。
規約：元の suspension は円との smash とする。
使われ方：自然性 square の水平辺と全合成列の両端の厳密な回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance suspensionCoherentDiagram_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- suspension の写像空間の頂点作用は、元の円との smash の射そのもの。 -/
lemma suspensionHom_vertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (suspensionHom X Y).right.app _ (pointedHomVertexEquiv X Y f) =
      pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)
        (PointedSimplicialSet.circle.{u} ◁ f) := by
  dsimp only [pointedHomVertexEquiv, Equiv.trans_apply, curryHomEquiv']
  change (suspensionHom X Y).right.app _
    (PointedSimplicialSet.unitVertexEquiv _ (curry' f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, suspensionHom_curry']
  rfl

/-- suspension 豊穣関手の通常の作用も元の円との smash の射を回収する。 -/
lemma suspensionEnrichedUnderlying_map {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor suspensionEnrichedFunctor).map f =
      PointedSimplicialSet.circle.{u} ◁ f := by
  apply (pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex suspensionEnrichedFunctor f
  change pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor suspensionEnrichedFunctor).map f) =
    (suspensionHom X Y).right.app _ (pointedHomVertexEquiv X Y f) at h
  exact h.trans (suspensionHom_vertex f)

/-- suspension 豊穣関手の通常の関手は元の円との smash 関手そのもの。 -/
lemma suspensionEnrichedUnderlying_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor suspensionEnrichedFunctor =
      MonoidalCategory.tensorLeft PointedSimplicialSet.circle.{u} := by
  refine CategoryTheory.Functor.ext (fun _ => ?_) ?_
  · rfl
  · intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact suspensionEnrichedUnderlying_map f

/-- Kan 包含の通常の作用は元の点つき射そのもの。 -/
lemma pointedKanInclusionUnderlying_map {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor pointedKanInclusionEnriched).map f = f.hom := by
  apply (pointedHomVertexEquiv X.obj Y.obj).injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex pointedKanInclusionEnriched f

/-- Kan 値の図式を包含して忘れると、全単体で元の通常の図式を回収する。 -/
lemma pointedKanInclusion_coherentDiagram {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :
    pointedKanCoherentDiagram F hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F := by
  have hf : pointedKanDiagram F hF ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor pointedKanInclusionEnriched = F := by
    refine CategoryTheory.Functor.ext (fun _ => ?_) ?_
    · rfl
    · intro i j f
      simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact (pointedKanInclusionUnderlying_map ((pointedKanDiagram F hF).map f)).trans (by rfl)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentDiagram_postcomp (pointedKanDiagram F hF)
    pointedKanInclusionEnriched).trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram hf)

end SerrePositivity.KST.SConstruction
