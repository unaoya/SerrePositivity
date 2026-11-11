module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.SuspensionComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedMappingLaws

/-!
概要：元の整合写像空間の合成を、点つきパラメータの smash から構成する。
方針：点つき閉構造の合成を各段で行い、構造条件を保つ族を普遍射へまとめる。
規約：一般の Kan 列を標的とする。使われ方：内部 Hom と Hom-end 交換の豊穣自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawPointedCompositionSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- suspension の内部 Hom への作用を、点つき自己豊穣関手へまとめる。 -/
def suspensionPointedEnrichedFunctor :
    EnrichedFunctor PointedSimplicialSet.{u} PointedSimplicialSet.{u} PointedSimplicialSet.{u} where
  obj := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension
  map := suspensionHom
  map_id := suspensionHom_id
  map_comp := suspensionHom_comp

/-- 点つき整合写像を各段で合成する実際の smash パラメータの射。 -/
def pointedCompositionFamily (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) (n : ℕ) :
    pointedSpace X Y.toKanSequence ⊗ pointedSpace Y Z ⟶
      PointedObject.basedHom (X.level n).space (Z.level n).space :=
  (pointedEvaluation X Y.toKanSequence n ⊗ₘ pointedEvaluation Y Z n) ≫
    MonoidalClosed.comp (X.level n).space (Y.level n).space (Z.level n).space

/-- smash パラメータの合成族も厳密な構造条件を保つ。 -/
lemma pointedCompositionFamily_condition (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) (n : ℕ) :
    pointedCompositionFamily X Y Z (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Z.level (n + 1)).space =
      pointedCompositionFamily X Y Z n ≫ pointedStep X Z n := by
  have ha := pointedEvaluation_condition X Y.toKanSequence n
  have hb := pointedEvaluation_condition Y Z n
  change pointedEvaluation X Y.toKanSequence (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space =
    pointedEvaluation X Y.toKanSequence n ≫
      (suspensionHom (X.level n).space (Y.level n).space ≫
        PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n)) at ha
  have hm (A B C : PointedSimplicialSet.{u}) (f : B ⟶ C) :
      PointedObject.basedHomMap A f = (ihom A).map f := rfl
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, pointedStep, hm] at ha hb
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_compatible_comp PointedSimplicialSet.{u} suspensionPointedEnrichedFunctor
    (X.sigma n) (Y.sigma n) (Z.sigma n)
    (pointedEvaluation X Y.toKanSequence n) (pointedEvaluation X Y.toKanSequence (n + 1))
    (pointedEvaluation Y Z n) (pointedEvaluation Y Z (n + 1))
    (by simpa only [enrichedOrdinaryCategorySelf_eHomWhiskerRight,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, suspensionPointedEnrichedFunctor,
      pointedStep, hm, Category.assoc] using ha)
    (by simpa only [enrichedOrdinaryCategorySelf_eHomWhiskerRight,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, suspensionPointedEnrichedFunctor,
      pointedStep, hm, Category.assoc] using hb)
  simpa only [pointedCompositionFamily, pointedStep, hm, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight, enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedCategorySelf_comp, suspensionPointedEnrichedFunctor, Category.assoc] using h

/-- 点つき全整合写像空間の実際の smash 合成。 -/
def pointedComposition (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    pointedSpace X Y.toKanSequence ⊗ pointedSpace Y Z ⟶ pointedSpace X Z :=
  pointedLift X Z (pointedCompositionFamily X Y Z)
    (fun n ↦ congrArg Under.Hom.right (pointedCompositionFamily_condition X Y Z n))

@[reassoc (attr := simp)]
lemma pointedComposition_evaluation (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) (n : ℕ) :
    pointedComposition X Y Z ≫ pointedEvaluation X Z n = pointedCompositionFamily X Y Z n :=
  pointedLift_evaluation _ _ _ _ n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
