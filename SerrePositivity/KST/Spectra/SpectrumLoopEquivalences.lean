module

public import SerrePositivity.KST.Spectra.OriginalLoopModelMap
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence

/-!
概要：元のスペクトルと一段先の loop の BF 模型の比較辺は、実際の Sp の同値。
方針：構成済みの厳密な比較射の全基点 π 同型性を、豊穣写像空間の可逆性判定へ渡す。
規約：群の同型だけから辺の可逆性を入力しない。使われ方：HA §1.4.2 の loop と添字移動の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance loopSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance loopHomKan (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 符号を調整した loop の BF 模型への単位は実際の Sp の同値。 -/
lemma signedLoopUnit_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (signedLoopUnit X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (signedLoopUnit_levelwise X)

/-- 通常と符号付きの loop の BF 模型の比較辺は実際の Sp の同値。 -/
lemma signedLoopComparison_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (signedLoopComparison X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (signedLoopComparison_levelwise X)

/-- 元のスペクトルから通常の loop の BF 模型への比較辺は実際の Sp の同値。 -/
lemma originalLoopModelMap_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (originalLoopModelMap X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (originalLoopModelMap_levelwise X)

/-- 元の対象と一段先の loop の BF 模型の具体的な頂点同型。 -/
def originalLoopModelVertexIso (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (rationalizationModel X)) := by
  haveI := originalLoopModelMap_isInvertible X
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (originalLoopModelMap X)))

end SerrePositivity.KST.Spectra.OmegaSpectrum
