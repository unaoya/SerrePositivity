module

public import SerrePositivity.KST.Spectra.SpectrumMappingStepEquivalence
public import SerrePositivity.KST.Spectra.SpectrumTailMappingPullback
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanRelativePathLifting

/-!
概要：一段の添字移動は実際の豊穣写像空間に同値を誘導する。
方針：零段の Ω 比較の同値を、境界評価の Kan fibration に沿って引き戻す。
規約：元の写像空間比較そのものの同値を証明する。使われ方：Sp の一段移動の完全忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 構造比較は全写像空間の実際の同値。 -/
lemma mappingStep_isQCatEquivalence (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (mappingStep X Y n) := by
  let s : PointedObject.basedHom (X.level n).space (Y.level n).space ⟶
      PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space :=
    suspensionHom _ _ ≫ PointedObject.basedHomMap _ (Y.sigma n)
  have h := pointed_piIsomorphism_homotopyEquivalence s (mappingStep_piIsomorphism X Y n)
  exact h.isQCatEquivalence

/-- 一段移動は元の豊穣 Hom から一段先の豊穣 Hom への実際の同値を誘導する。 -/
lemma tailMapping_isQCatEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (tailMapping X Y) := by
  let p := tailMappingBoundary X Y
  have : Fibration p := tailMappingBoundary_fibration X Y
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p 1
  have hp := (mappingStep_isQCatEquivalence X Y 0).pullback_snd_of_relativePath p
  let e := (tailMapping_isPullback X Y).isoPullback
  have he : e.hom ≫ pullback.snd (mappingStep X Y 0) p = tailMapping X Y :=
    IsPullback.isoPullback_hom_snd _
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.comp hp

/-- 一段移動の豊穣 Hom 比較は単体的ホモトピー同値でもある。 -/
lemma tailMapping_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (tailMapping X Y) :=
  (tailMapping_isQCatEquivalence X Y).isSimplicialHomotopyEquivalence

/-- 一段移動の実際の写像空間比較を、逆射とともに束ねる。 -/
def tailMappingEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (mappingSpace X Y) (mappingSpace (tail X) (tail Y)) :=
  (tailMapping_isQCatEquivalence X Y).choose

/-- 束ねた同値の順射は元の整合族から零段を落とす比較そのもの。 -/
lemma tailMappingEquivalence_hom (X Y : OmegaSpectrum.{u}) :
    (tailMappingEquivalence X Y).hom = tailMapping X Y := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
