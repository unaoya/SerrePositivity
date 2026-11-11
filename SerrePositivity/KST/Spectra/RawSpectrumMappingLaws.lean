module

public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-!
概要：一般の Kan 列への後合成の法則と、実際の BF 豊穣 Hom の後合成との一致。
方針：全切断の外延性で各段評価へ戻す。
規約：BF の場合も新しい写像空間へ置き換えない。使われ方：cotensor・end の比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- Kan 列の恒等射による後合成は恒等。 -/
lemma post_id (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    post X (⟨fun _ ↦ 𝟙 _, by intro n; simp⟩ : KanSequence.Hom Y Y) = 𝟙 (space X Y) := by
  apply hom_ext X Y
  intro n
  rw [post_evaluation, Category.id_comp]
  change evaluation X Y n ≫ (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (X.level n).space).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id]
  change evaluation X Y n ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Kan 列の射の合成による後合成は、実際の写像空間上でも合成。 -/
lemma post_comp (X : OmegaSpectrum.{u}) {Y Z W : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (q : KanSequence.Hom Z W) :
    post X (p.comp q) = post X p ≫ post X q := by
  apply hom_ext X W
  intro n
  rw [Category.assoc, post_evaluation, post_evaluation, ← Category.assoc, post_evaluation]
  change evaluation X Y n ≫ (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (X.level n).space).map
    (p.app n ≫ q.app n) = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

local instance rawSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- BF 標的の場合、後合成は元の豊穣写像空間の後合成そのもの。 -/
lemma post_spectrum (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) :
    post X (⟨p.app, p.comm⟩ : KanSequence.Hom Y.toKanSequence Z.toKanSequence) =
      ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p := by
  apply hom_ext X Z.toKanSequence
  intro n
  rw [post_evaluation]
  exact (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomMap_evaluation X p n).symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
