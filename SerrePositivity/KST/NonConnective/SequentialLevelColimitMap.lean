module

public import SerrePositivity.KST.NonConnective.SequentialCofibrantColimit
public import SerrePositivity.KST.Spectra.FilteredSpectrumMap

/-!
概要：元の段ごとの BF 余極限の、厳密な比較自然変換に対する作用。
方針：元の BF 余錐への普遍射を作り、各段で pointed 余極限の比較と照合する。
規約：比較射そのものの全整数 π 同型性を証明する。
使われ方：相対置換列の実余極限性を元の厳密な余錐に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 比較自然変換と元の余錐の脚を合成した、置換元上の実 BF 余錐。 -/
def sequentialLevelComparisonCocone {D E : SpectrumSequence.{u}} (η : D ⟶ E) : Cocone D where
  pt := sequentialLevelColimitSpectrum E
  ι := η ≫ (sequentialLevelColimitCocone E).ι

/-- 元の通常の BF 普遍射から得る、段ごとの余極限の比較。 -/
def sequentialLevelColimitMap {D E : SpectrumSequence.{u}} (η : D ⟶ E) :
    sequentialLevelColimitSpectrum D ⟶ sequentialLevelColimitSpectrum E :=
  sequentialLevelColimitDesc D (sequentialLevelComparisonCocone η)

/-- 元の比較と元の余錐の各脚は厳密に可換。 -/
lemma sequentialLevelColimitMap_fac {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (a : SequentialIndex.{u}) :
    sequentialLevelColimitInjection D a ≫ sequentialLevelColimitMap η =
      η.app a ≫ sequentialLevelColimitInjection E a :=
  (sequentialLevelColimitIsColimit D).fac (sequentialLevelComparisonCocone η) a

/-- 同じ比較の各段は、pointed 余極限の元の比較射。 -/
lemma sequentialLevelColimitMap_app {D E : SpectrumSequence.{u}} (η : D ⟶ E) (k : ℕ) :
    (sequentialLevelColimitMap η).app k = colimMap (OmegaSpectrum.levelTransformation η k) := by
  apply colimit.hom_ext
  intro a
  exact (congrArg (fun f ↦ f.app k) (sequentialLevelColimitMap_fac η a)).trans
    (colimit.ι_map (OmegaSpectrum.levelTransformation η k) a).symm

/-- 同じ元の比較が各段で全整数 π 同型なら、同じ BF 余極限比較も全整数 π 同型。 -/
lemma sequentialLevelColimitMap_piIsomorphism {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ a, OmegaSpectrum.PiIsomorphism (η.app a)) :
    OmegaSpectrum.PiIsomorphism (sequentialLevelColimitMap η) := by
  apply OmegaSpectrum.piIsomorphism_of_levelwise
  intro k
  rw [sequentialLevelColimitMap_app]
  exact pointedColimMap_kanPiIsomorphism (OmegaSpectrum.levelTransformation η k)
    (fun a ↦ (hη a).levelwise k)

end SerrePositivity.KST.NonConnective
