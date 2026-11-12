module
public import SerrePositivity.KST.Fibration.DGKPositiveEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage
public import SerrePositivity.KST.Spectra.Limits.SpectrumMappingDiagram

/-! # 元の BF 段評価の、同じ通常射と点つき値の回収 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance evaluationOrdinarySpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance evaluationOrdinaryPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 同じ厳密豊穣評価から得る、元の点つき Kan 段への通常の関手。 -/
abbrev spectrumKanEvaluationOrdinary (n : ℕ) : OmegaSpectrum.{u} ⥤ PointedKanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (spectrumKanEvaluation n)

/-- 元の BF 射を評価すると、同じ元の段射 app n そのものが得られる。 -/
theorem spectrumKanEvaluationOrdinary_map (n : ℕ) {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    (spectrumKanEvaluationOrdinary n).map f = ObjectProperty.homMk (f.app n) := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (spectrumKanEvaluation n) f = _
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_of_hom
  have hf : eHomEquiv SSet f = OmegaSpectrum.vertexOfHomMap f := by
    change (SSet.unitHomEquiv _).symm
      ((SSet.unitHomEquiv _) (OmegaSpectrum.vertexOfHomMap f)) = _
    exact Equiv.symm_apply_apply _ _
  rw [hf]
  change OmegaSpectrum.vertexOfHomMap f ≫ OmegaSpectrum.evaluation X Y n =
    eHomEquiv SSet (f.app n)
  exact OmegaSpectrum.vertexOfHomMap_evaluation f n

/-- Kan 性だけを忘れると、元の同じ点つき段評価と厳密に一致する。 -/
theorem spectrumKanEvaluationOrdinary_forget (n : ℕ) :
    spectrumKanEvaluationOrdinary.{u} n ⋙ pointedKanProperty.ι = _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((spectrumKanEvaluationOrdinary n).map f).hom = f.app n
  exact congrArg (fun g => g.hom) (spectrumKanEvaluationOrdinary_map n f)

end SerrePositivity.KST.Fibration
