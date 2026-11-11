module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedTail
public import SerrePositivity.KST.Spectra.SpectrumTailMappingEquivalence
public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
概要：一般の Ω Kan 列を標的とする元の全 Hom でも、一段移動自身は全基点 π 同型。
方針：BF 置換の段ごとの全単射 RLP と後合成自然性で、既存の BF 一段移動を移す。
規約：元の一段移動の射を保持。使われ方：元の評価写像の一段移動による同型性の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- Ω 標的への全 Hom の零段を忘れる元の射は、全基点 π 同型。 -/
lemma pointedTail_piIsomorphism (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (hY : Y.OmegaCondition) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedTail X Y).right := by
  let W := Y.cofibrantOmegaSpectrum hY
  let q := Y.cofibrantOmegaProjection hY
  have hq (n : ℕ) : (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right :=
    (Y.replacementStage n).projection_rlp
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost X q).right := post_piIsomorphism X q hq
  have hr : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (pointedPost (OmegaSpectrum.tail X) (KanSequence.tailHom q)).right :=
    post_piIsomorphism (OmegaSpectrum.tail X) (KanSequence.tailHom q) (fun n => hq (n + 1))
  have ht : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedTail X W.toKanSequence).right := by
    rw [pointedTail_BF_right]
    exact kanPiIsomorphism_of_qCatEquivalence _ (OmegaSpectrum.tailMapping_isQCatEquivalence X W)
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((pointedPost X q).right ≫ (pointedTail X Y).right) := by
    rw [← Under.comp_right, pointedTail_post, Under.comp_right]
    exact ht.comp hr
  exact (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex hp) hc (pointedSpace X W.toKanSequence).basepoint

end SerrePositivity.KST.Spectra.RawSpectrumMapping
