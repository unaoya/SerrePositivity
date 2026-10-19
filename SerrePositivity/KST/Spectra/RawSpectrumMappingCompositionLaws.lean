module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingComposition

/-!
概要：一般の Kan 列を標的とする全整合写像の合成の法則。
方針：全段の評価で BF の合成・単位と、各段の豊穣結合律・後合成を比較する。
規約：全 Hom パラメータの射の等式。使われ方：Hom-end 比較の豊穣自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawCompositionLawsPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- BF 標的の場合、構成した合成は元の豊穣合成そのもの。 -/
lemma composition_spectrum (X Y Z : OmegaSpectrum.{u}) :
    composition X Y Z.toKanSequence = OmegaSpectrum.mappingComposition X Y Z := rfl

/-- 一般の Kan 列を標的としても、豊穣 Hom の恒等射は合成の左単位。 -/
lemma identity_composition (X : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    (λ_ (space X Z)).inv ≫ OmegaSpectrum.mappingIdentity X ▷ space X Z ≫
      composition X X Z = 𝟙 _ := by
  apply hom_ext X Z
  intro n
  simp only [Category.assoc, composition_evaluation, compositionFamily, Category.id_comp]
  rw [whiskerRight_comp_tensorHom_assoc, OmegaSpectrum.mappingIdentity_evaluation,
    leftUnitor_inv_comp_tensorHom_assoc]
  exact (congrArg (fun k ↦ evaluation X Z n ≫ k)
    (e_id_comp SSet (X.level n).space (Z.level n).space)).trans (Category.comp_id _)

/-- 元の BF 豊穣合成と一般の Kan 列への合成は、全パラメータで結合的。 -/
lemma composition_assoc (W X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    (α_ (OmegaSpectrum.mappingSpace W X) (OmegaSpectrum.mappingSpace X Y) (space Y Z)).inv ≫
      OmegaSpectrum.mappingComposition W X Y ▷ space Y Z ≫ composition W Y Z =
    OmegaSpectrum.mappingSpace W X ◁ composition X Y Z ≫ composition W X Z := by
  apply hom_ext W Z
  intro n
  simp only [Category.assoc, composition_evaluation, compositionFamily]
  rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    OmegaSpectrum.mappingComposition_evaluation, composition_evaluation]
  simp only [compositionFamily, OmegaSpectrum.compositionFamily]
  rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
    Category.assoc, ← associator_inv_naturality_assoc]
  simp only [Category.assoc]
  exact congrArg (fun k ↦
    (OmegaSpectrum.evaluation W X n ⊗ₘ (OmegaSpectrum.evaluation X Y n ⊗ₘ evaluation Y Z n)) ≫ k)
      (e_assoc SSet (W.level n).space (X.level n).space (Y.level n).space (Z.level n).space)

/-- 一般の Kan 列の射の後合成は、BF Hom の全パラメータによる合成と厳密に可換。 -/
lemma composition_post (X Y : OmegaSpectrum.{u}) {Z T : KanSequence.{u}}
    (p : KanSequence.Hom Z T) :
    composition X Y Z ≫ post X p =
      (𝟙 (OmegaSpectrum.mappingSpace X Y) ⊗ₘ post Y p) ≫ composition X Y T := by
  apply hom_ext X T
  intro n
  rw [Category.assoc, post_evaluation, ← Category.assoc, composition_evaluation]
  conv_rhs =>
    rw [Category.assoc, composition_evaluation]
    dsimp only [compositionFamily]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, post_evaluation]
  dsimp only [compositionFamily]
  rw [Category.assoc, ← PointedEnrichment.whiskerLeft_eq, eComp_eHomWhiskerLeft,
    ← Category.assoc]
  rw [PointedEnrichment.whiskerLeft_eq]
  exact congrArg (fun f ↦ f ≫
    eComp SSet (X.level n).space (Y.level n).space (T.level n).space)
      (tensorHom_comp_whiskerLeft (OmegaSpectrum.evaluation X Y n) (evaluation Y Z n)
        (PointedObject.basedHomMap (Y.level n).space (p.app n)).right)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
