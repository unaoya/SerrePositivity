module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalPath
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.KST.LocalizingInvariants.FullyFaithfulEdgeRealization

/-!
概要：Sp の標準区間 Hom の指定射の類を、同じ端点を持つ実 BF 区間で実現する。
方針：coherent 区間比較の充満忠実性で射を戻し、辺代表を元の宇宙へ降ろす。
規約：区間 Hom 内の射の類を保持し、Sp の辺の π₀ の一致には弱めない。
使われ方：元の三角形を保つ相対 prism の対角の BF 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath

local instance pathRealizationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance pathRealizationKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

variable {X Y : OmegaSpectrum.{u}} (f g : X ⟶ Y)
local notation "C" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y

structure NormalizedIntervalRealization
    (α : HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g))) where
  path : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g)
  image : Truncated.HomotopyCategory.homMk (intervalEdge path).toTruncated = α

def normalizedIntervalRealization
    (α : HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g))) :
    NormalizedIntervalRealization f g α := by
  let R := transportedEdgeRealization (C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_isQCatEquivalence X Y).isFullyFaithful
    (ULift.up (vertexOfHom f)) (ULift.up (vertexOfHom g)) (interval_vertex f) (interval_vertex g) α
  let P : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g) :=
    SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge R.path.toTruncated)
  have he : (intervalEdge P).toTruncated =
      ((R.path.map C).ofEq (interval_vertex f) (interval_vertex g)).toTruncated := by
    apply Truncated.Edge.ext
    exact congrArg (fun z ↦ (C).app (Opposite.op ⦋1⦌) z) (ULift.up_down R.path.edge)
  exact ⟨P, (congrArg Truncated.HomotopyCategory.homMk he).trans R.image⟩

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
