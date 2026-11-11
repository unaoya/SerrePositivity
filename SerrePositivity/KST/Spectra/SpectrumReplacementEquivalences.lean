module

public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence
public import SerrePositivity.KST.Spectra.OmegaSpectrumReplacedTotalization
public import SerrePositivity.KST.Spectra.OmegaSpectrumTotalizationComparison

/-!
概要：既存の BF fibration 置換と通常 Tot の比較射を、本レーンの Sp の同値として公開する。
方針：実際の各段の全基点 π 同型を、豊穣 Hom で検証した Whitehead 判定へ渡す。
規約：元の比較射の coherent な辺そのものを使う。新しい Sp の模型を定義しない。
使われ方：HTT A.3.3、HA §1.4.2。∞ 極限との合流と局所化不変量の値域。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
noncomputable section
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 既存の BF fibration 置換単位は実際の Sp の同値。 -/
lemma fibrationReplacementUnit_isInvertible {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementUnit f)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (fibrationReplacementUnit_levelwise f)

/-- 段ごとの π 同型の fibration 置換の射影も実際の Sp の同値。 -/
lemma fibrationReplacementProjection_isInvertible {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection f)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (fun n ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (SpectrumMappingAcyclic.projection_rlp f hf n))

/-- Reedy 条件下の通常 Tot の比較射は実際の Sp の同値。 -/
lemma ordinaryTotalizationComparison_isInvertible (X : CosimplicialObject OmegaSpectrum.{u})
    (hX : KanSequence.TotalizationReedy (X ⋙ forgetToKan)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (ordinaryTotalizationComparison X hX)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (ordinaryTotalizationComparison_levelwise X hX)

/-- 任意の図式の Reedy 置換した通常 Tot と元の homotopy Tot は実際の Sp の同値。 -/
lemma replacedOrdinaryTotalizationComparison_isInvertible
    (X : CosimplicialObject OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (replacedOrdinaryTotalizationComparison X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _
    (replacedOrdinaryTotalizationComparison_levelwise X)

end
end SerrePositivity.KST.Spectra.OmegaSpectrum
