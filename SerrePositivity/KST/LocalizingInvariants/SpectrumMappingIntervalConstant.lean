module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalPath

/-!
概要：BF の定数区間は、Sp の辺の関手圏でも同じ恒等辺に写る。
方針：coherent 区間 Hom 比較と fiber 包含の退化との可換性を計算する。
規約：恒等性は辺そのものの等式。使われ方：置換単位の射影に垂直な全族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath

local instance constantPathCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)

lemma intervalEdge_id : intervalEdge (SSet.Edge.id (vertexOfHom f)) =
    SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) := by
  apply SSet.Edge.ext
  exact (SSet.σ_naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) 0
    (ULift.up (vertexOfHom f))).trans
      (congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)).σ 0 z) (interval_vertex f))

lemma arrowEdge_id : arrowEdge (SSet.Edge.id (vertexOfHom f)) =
    SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) := by
  change (intervalEdge (SSet.Edge.id (vertexOfHom f))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) = _
  rw [intervalEdge_id]
  apply SSet.Edge.ext
  exact SSet.σ_naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) 0 _

lemma intervalEdge_constant (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom f))
    (h : e = SSet.Edge.id (vertexOfHom f)) : (intervalEdge e).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) 1 := by
  exact (congrArg (fun k ↦ (intervalEdge k).edge) h).trans
    ((congrArg SSet.Edge.edge (intervalEdge_id f)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm)

lemma intervalEdge_congr {f₀ g₀ f₁ g₁ : X ⟶ Y}
    (e₀ : (mappingSpace X Y).Edge (vertexOfHom f₀) (vertexOfHom g₀))
    (e₁ : (mappingSpace X Y).Edge (vertexOfHom f₁) (vertexOfHom g₁))
    (h : e₀.edge = e₁.edge) : (intervalEdge e₀).edge = (intervalEdge e₁).edge :=
  congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y).app
    (Opposite.op ⦋1⦌) (ULift.up z)) h

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
