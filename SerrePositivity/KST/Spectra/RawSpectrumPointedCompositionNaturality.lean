module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedComposition
public import SerrePositivity.KST.Spectra.RawSpectrumMappingFunctor

/-!
概要：点つき全整合写像の合成と、一般の Kan 列の射の後合成の両立。
方針：各段で閉構造の合成の標的に関する自然性を使う。
規約：全 smash パラメータの射の等式。使われ方：Hom–end の豊穣自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance pointedCompositionPostSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 全 smash パラメータによる合成は、任意の Kan 列の後合成と可換。 -/
lemma pointedComposition_post (X Y : OmegaSpectrum.{u}) {Z T : KanSequence.{u}} (p : Z ⟶ T) :
    pointedComposition X Y Z ≫ pointedPost X p =
      (𝟙 (pointedSpace X Y.toKanSequence) ⊗ₘ pointedPost Y p) ≫ pointedComposition X Y T := by
  apply pointed_hom_ext X T
  intro n
  rw [Category.assoc, pointedPost_evaluation, ← Category.assoc, pointedComposition_evaluation]
  conv_rhs =>
    rw [Category.assoc, pointedComposition_evaluation]
    dsimp only [pointedCompositionFamily]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, pointedPost_evaluation]
  dsimp only [pointedCompositionFamily]
  have h := eComp_eHomWhiskerLeft PointedSimplicialSet.{u}
    (X.level n).space (Y.level n).space (p.app n)
  simp only [enrichedCategorySelf_comp, enrichedOrdinaryCategorySelf_eHomWhiskerLeft] at h
  change _ ≫ (ihom (X.level n).space).map (p.app n) = _
  rw [Category.assoc, h, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ comp (X.level n).space (Y.level n).space (T.level n).space)
    (tensorHom_comp_whiskerLeft (pointedEvaluation X Y.toKanSequence n)
      (pointedEvaluation Y Z n) ((ihom (Y.level n).space).map (p.app n)))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
