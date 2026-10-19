module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedComposition

/-!
概要：全整合写像空間の点つき合成の単位を構成する。
方針：元の BF 恒等射の頂点を零次球面からの射へ戻し、各段で単位律を検査する。
規約：全 smash パラメータに対する厳密な等式。
使われ方：cotensor の普遍評価から元の Hom 比較を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance pointedUnitsSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 元の BF 恒等射を表す、点つき豊穣 Hom の単位。 -/
def pointedIdentity (X : OmegaSpectrum.{u}) :
    𝟙_ PointedSimplicialSet.{u} ⟶ pointedSpace X X.toKanSequence :=
  (PointedSimplicialSet.unitVertexEquiv _).symm (OmegaSpectrum.vertexOfHom (𝟙 X))

/-- 点つき単位の段評価はその段の閉構造の単位。 -/
@[reassoc (attr := simp)]
lemma pointedIdentity_evaluation (X : OmegaSpectrum.{u}) (n : ℕ) :
    pointedIdentity X ≫ pointedEvaluation X X.toKanSequence n =
      curry' (𝟙 (X.level n).space) := by
  apply (PointedSimplicialSet.unitVertexEquiv _).injective
  rw [PointedSimplicialSet.unitVertexEquiv_naturality]
  dsimp only [pointedIdentity]
  rw [Equiv.apply_symm_apply]
  change (OmegaSpectrum.evaluation X X n).app _ (OmegaSpectrum.vertexOfHom (𝟙 X)) = _
  rw [OmegaSpectrum.vertexOfHom_evaluation]
  rfl

/-- 全整合写像の点つき合成の右単位律。 -/
lemma pointedComposition_identity (X Y : OmegaSpectrum.{u}) :
    (ρ_ (pointedSpace X Y.toKanSequence)).inv ≫
      pointedSpace X Y.toKanSequence ◁ pointedIdentity Y ≫
        pointedComposition X Y Y.toKanSequence = 𝟙 _ := by
  apply pointed_hom_ext X Y.toKanSequence
  intro n
  simp only [Category.assoc, pointedComposition_evaluation, pointedCompositionFamily,
    Category.id_comp]
  rw [whiskerLeft_comp_tensorHom_assoc, pointedIdentity_evaluation,
    rightUnitor_inv_comp_tensorHom_assoc]
  change pointedEvaluation X Y.toKanSequence n ≫
    (ρ_ ((ihom (X.level n).space).obj (Y.level n).space)).inv ≫
      ((ihom (X.level n).space).obj (Y.level n).space) ◁
        curry' (𝟙 (Y.level n).space) ≫
          comp (X.level n).space (Y.level n).space (Y.level n).space = _
  rw [whiskerLeft_curry'_comp]
  simp

/-- 全整合写像の点つき合成の左単位律。 -/
lemma pointedIdentity_composition (X : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    (λ_ (pointedSpace X Z)).inv ≫ pointedIdentity X ▷ pointedSpace X Z ≫
      pointedComposition X X Z = 𝟙 _ := by
  apply pointed_hom_ext X Z
  intro n
  simp only [Category.assoc, pointedComposition_evaluation, pointedCompositionFamily,
    Category.id_comp]
  rw [whiskerRight_comp_tensorHom_assoc, pointedIdentity_evaluation,
    leftUnitor_inv_comp_tensorHom_assoc]
  change pointedEvaluation X Z n ≫
    (λ_ ((ihom (X.level n).space).obj (Z.level n).space)).inv ≫
      curry' (𝟙 (X.level n).space) ▷ ((ihom (X.level n).space).obj (Z.level n).space) ≫
        comp (X.level n).space (X.level n).space (Z.level n).space = _
  rw [curry'_whiskerRight_comp]
  simp

end SerrePositivity.KST.Spectra.RawSpectrumMapping
