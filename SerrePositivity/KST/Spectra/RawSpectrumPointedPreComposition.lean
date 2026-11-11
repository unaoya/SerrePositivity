module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition
public import SerrePositivity.KST.Spectra.RawSpectrumPointedComposition

/-!
概要：元の点つき全写像空間の smash 合成と、BF 源の厳密射による前合成の可換式。
方針：全段の評価で閉モノイダル圏の豊穣合成の源自然性を照合する。
規約：全 Hom パラメータの厳密な式。
使われ方：普遍評価と元の evaluationPost のパラメータ自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance pointedPreCompositionSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 元の smash 合成の後の源制限は、第一パラメータを先に制限する同じ合成。 -/
lemma pointedComposition_pre {W V : OmegaSpectrum.{u}} (f : W ⟶ V)
    (X : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    pointedComposition V X Z ≫ pointedPre f Z =
      pointedPre f X.toKanSequence ▷ pointedSpace X Z ≫ pointedComposition W X Z := by
  apply pointed_hom_ext W Z
  intro n
  rw [Category.assoc, pointedPre_evaluation, ← Category.assoc, pointedComposition_evaluation]
  conv_rhs =>
    rw [Category.assoc, pointedComposition_evaluation]
    dsimp only [pointedCompositionFamily]
    rw [whiskerRight_comp_tensorHom_assoc, pointedPre_evaluation]
  have hc := eComp_eHomWhiskerRight PointedSimplicialSet.{u} (f.app n)
    (X.level n).space (Z.level n).space
  simp only [enrichedCategorySelf_comp, enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hc
  dsimp only [pointedCompositionFamily]
  rw [Category.assoc, hc, ← Category.assoc]
  exact congrArg (· ≫ MonoidalClosed.comp
    (W.level n).space (X.level n).space (Z.level n).space)
    (tensorHom_comp_whiskerRight (pointedEvaluation V X.toKanSequence n)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (f.app n) (X.level n).space) (pointedEvaluation X Z n))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
