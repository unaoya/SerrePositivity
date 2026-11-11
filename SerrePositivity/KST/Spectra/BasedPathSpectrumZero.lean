module

public import SerrePositivity.KST.Spectra.BasedPathSpectrum
public import SerrePositivity.KST.Spectra.BoundaryFilling
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：基点付き path の BF 模型は実際の Sp の零対象に同値。
方針：path の終対象への全単射 RLP と BF 置換射影の RLP を合成し、元の辺の可逆性を得る。
規約：全基点を扱い、群の自明性だけから同値性を仮定しない。使われ方：Sp の loop 錐の零角。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 基点付き path から一点への点つき射も全単射 RLP を持つ。 -/
lemma basedPathSpace_toPoint_rlp (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (PointedObject.toPoint (basedPathSpace Y)).right := by
  let e : (⊤_ SSet.{u}) ≅ 𝟙_ SSet.{u} :=
    terminalIsTerminal.uniqueUpToIso isTerminalTensorUnit
  have h : (PointedObject.toPoint (basedPathSpace Y)).right =
      terminal.from (basedPathSpace Y).right ≫ e.hom := isTerminalTensorUnit.hom_ext _ _
  rw [h]
  exact (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (basedPathSpace_terminal_rlp Y)
    ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso e.hom)

namespace OmegaSpectrum

/-- BF path 模型から一点スペクトルへの実際の射。 -/
def basedPathToPoint (Y : OmegaSpectrum.{u}) : basedPath Y ⟶ _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from _

/-- 各段は元の path の BF 射影の後に一点へ進む。 -/
lemma basedPathToPoint_app (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (basedPathToPoint Y).app n = (cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).app n ≫
      PointedObject.toPoint (basedPathSpace (Y.level n).space) :=
  PointedObject.point_isZero.eq_of_tgt _ _

/-- BF path 模型から一点への射は各段で全単射 RLP を持つ。 -/
lemma basedPathToPoint_rlp (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((basedPathToPoint Y).app n).right := by
  rw [basedPathToPoint_app, Under.comp_right]
  exact (MorphismProperty.monomorphisms SSet.{u}).rlp.comp_mem _ _
    (KanSequence.replacementStage
      (KanSequence.mapping _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} Y.toKanSequence) n).projection_rlp
    (basedPathSpace_toPoint_rlp (Y.level n).space)

lemma basedPathToPoint_levelwise (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((basedPathToPoint Y).app n).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (basedPathToPoint_rlp Y n)

local instance pathZeroSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance pathZeroHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 元の BF path から一点への辺は実際の Sp の同値。 -/
lemma basedPathToPoint_isInvertible (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathToPoint Y)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (basedPathToPoint_levelwise Y)

/-- BF path 模型と一点スペクトルの具体的な頂点同型。 -/
def basedPathPointIso (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (basedPath Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint) := by
  haveI := basedPathToPoint_isInvertible Y
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathToPoint Y)))

/-- BF path の頂点は実際の Sp の零頂点。 -/
lemma basedPath_isZeroVertex (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (basedPath Y)) :=
  pointZeroVertex.isZero.of_vertexIso (basedPathPointIso Y).symm

end OmegaSpectrum
end SerrePositivity.KST.Spectra
