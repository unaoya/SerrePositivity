module

public import SerrePositivity.KST.Spectra.SpectrumTailMappingEquivalence
public import SerrePositivity.KST.Spectra.SpectrumLoopTailComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：一段の添字移動は元の Sp の実際の ∞ 圏同値。
方針：全豊穣写像空間上の同値性と既証の本質的全射性を coherent nerve の判定へ渡す。
規約：群の同型だけから圏の同値を推論しない。使われ方：Sp の loop と安定性の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance tailEquivSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance tailEquivHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 一段移動の元の関手は全写像空間の意味で完全忠実。 -/
lemma nativeTail_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful nativeTail.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff tailEnriched).2 tailMapping_isQCatEquivalence

/-- 元の Sp の一段移動は逆と可逆二胞体を持つ実際の同値。 -/
def nativeTailEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Sp.{u} Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective nativeTail
    nativeTail_isFullyFaithful nativeTail_essentiallySurjective

/-- 構成した同値の順方向は元の一段移動関手。 -/
lemma nativeTailEquivalence_hom : nativeTailEquivalence.{u}.hom = nativeTail := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
