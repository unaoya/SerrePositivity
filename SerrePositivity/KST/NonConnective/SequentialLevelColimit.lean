module

public import SerrePositivity.KST.NonConnective.FilteredExchangeLevelColimit
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
概要：段ごとの filtered Kan 余極限自体の BF 単射条件。
方針：単体集合の filtered 余極限が単射を保存することを suspension の余極限保存と合わせる。
規約：通常の BF 余錐を構成し、∞ 余極限性は後で判定する。
使われ方：K-7 の反変 Hom の普遍性の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 段ごとの逐次 Kan 余極限の構造射も単射である。 -/
lemma sequentialKanSequence_sigma_mono (D : SpectrumSequence.{u}) (k : ℕ) :
    Mono ((OmegaSpectrum.filteredKanSequence D).sigma k).right :=
  FilteredExchange.kanSequence_sigma_mono D k

/-- 単射条件も持つ、置換前の段ごとの余極限 BF 対象。 -/
def sequentialLevelColimitSpectrum (D : SpectrumSequence.{u}) : OmegaSpectrum.{u} :=
  (OmegaSpectrum.filteredKanSequence D).toOmegaSpectrum
    (sequentialKanSequence_sigma_mono D) (OmegaSpectrum.filteredKanSequence_omegaCondition D)

/-- 段ごとの標準注入は置換前の BF 対象への厳密射でもある。 -/
def sequentialLevelColimitInjection (D : SpectrumSequence.{u}) (a : SequentialIndex.{u}) :
    D.obj a ⟶ sequentialLevelColimitSpectrum D where
  app := (OmegaSpectrum.filteredKanInjection D a).app
  comm := (OmegaSpectrum.filteredKanInjection D a).comm

/-- 元の BF 図式に対する、段ごとの余極限を頂点とする厳密な通常余錐。 -/
def sequentialLevelColimitCocone (D : SpectrumSequence.{u}) : Cocone D where
  pt := sequentialLevelColimitSpectrum D
  ι := {
    app := sequentialLevelColimitInjection D
    naturality _ _ f := by
      apply OmegaSpectrum.Hom.ext
      intro k
      exact colimit.w (OmegaSpectrum.levelDiagram D k) f }

/-- 既存の BF 置換から、置換前の BF 余極限への同じ射影。 -/
def sequentialReplacementProjection (D : SpectrumSequence.{u}) :
    sequentialSpectrum D ⟶ sequentialLevelColimitSpectrum D where
  app := (OmegaSpectrum.filteredSequenceComparison D).app
  comm := (OmegaSpectrum.filteredSequenceComparison D).comm

/-- 上の同じ実射影は全整数の π 同型。 -/
lemma sequentialReplacementProjection_piIsomorphism (D : SpectrumSequence.{u}) :
    OmegaSpectrum.PiIsomorphism (sequentialReplacementProjection D) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (OmegaSpectrum.filteredLevelComparison_piIsomorphism D)

end SerrePositivity.KST.NonConnective
