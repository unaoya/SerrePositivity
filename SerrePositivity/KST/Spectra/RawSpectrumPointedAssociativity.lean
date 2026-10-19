module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedUnits

/-!
概要：全整合写像空間の点つき合成の結合律。
方針：各段へ評価し、閉構造の自己豊穣の結合律を適用する。
規約：全 smash パラメータでの厳密な等式。
使われ方：普遍評価と可換な射の組の豊穣圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance pointedAssocSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 元の点つき全写像空間の合成は、全パラメータで結合的。 -/
lemma pointedComposition_assoc (W X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    (α_ (pointedSpace W X.toKanSequence) (pointedSpace X Y.toKanSequence)
      (pointedSpace Y Z)).inv ≫
      pointedComposition W X Y.toKanSequence ▷ pointedSpace Y Z ≫
        pointedComposition W Y Z =
      pointedSpace W X.toKanSequence ◁ pointedComposition X Y Z ≫
        pointedComposition W X Z := by
  apply pointed_hom_ext W Z
  intro n
  simp only [Category.assoc, pointedComposition_evaluation, pointedCompositionFamily]
  rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    pointedComposition_evaluation, pointedComposition_evaluation]
  dsimp only [pointedCompositionFamily]
  rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
    Category.assoc, ← associator_inv_naturality_assoc]
  simp only [Category.assoc]
  exact congrArg (fun k ↦
    (pointedEvaluation W X.toKanSequence n ⊗ₘ
      (pointedEvaluation X Y.toKanSequence n ⊗ₘ pointedEvaluation Y Z n)) ≫ k)
    (MonoidalClosed.assoc (W.level n).space (X.level n).space (Y.level n).space
      (Z.level n).space)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
