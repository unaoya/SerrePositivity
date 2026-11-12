module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionNaturality
public import SerrePositivity.KST.LocalizingInvariants.CoherentCompositionTriangleVertex
public import SerrePositivity.KST.LocalizingInvariants.PrismEdgeEndpoint

/-!
概要：BF 後合成 prism の端点を、元の通常の合成三角形に厳密に同定する。
方針：同じ豊穣辺の二端に制限し、固定パラメーターの合成二単体を計算する。
規約：相対ホモトピーの存在で端点の等号を代用しない。使われ方：模型比較の標準表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumPostcomposition

local instance postEndpointsCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) {f g : X ⟶ Y}
  (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g))

lemma prism_parameter : SpectrumMappingPath.postTrianglePrism p e =
    (Δ[2] ◁ SSet.yonedaEquiv.symm (SpectrumMappingPath.liftedEdge e).edge) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionFixedTriangle X Y Z p := by
  have he : SSet.yonedaEquiv.symm (SpectrumMappingPath.postTriangleEdge p e).edge =
      SSet.yonedaEquiv.symm (SpectrumMappingPath.liftedEdge e).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence X Y Z p :=
    (SSet.yonedaEquiv_symm_comp _ _).symm
  rw [SpectrumMappingPath.postTrianglePrism, he, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCompositionCorrespondence_evaluation]

lemma sourceTriangle_eq : sourceTriangle p e =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f p).simplex := by
  have he : sourceTriangle p e =
      lift (𝟙 (Δ[2] : SSet.{u + 1}))
        (SSet.const (ULift.up (SimplicialCategory.homEquiv' X Y f))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionFixedTriangle X Y Z p := by
    rw [sourceTriangle, prism_parameter, ← Category.assoc, prismEdge_source]
    rw [SpectrumMappingAcyclic.homEquiv'_eq_vertex]
  apply SSet.yonedaEquiv.injective
  exact ((congrArg SSet.yonedaEquiv he).trans
    (coherentCompositionFixedTriangle_vertex _ _)).trans
      (SSet.yonedaEquiv.apply_symm_apply _).symm

lemma targetTriangle_eq : targetTriangle p e =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct g p).simplex := by
  have he : targetTriangle p e =
      lift (𝟙 (Δ[2] : SSet.{u + 1}))
        (SSet.const (ULift.up (SimplicialCategory.homEquiv' X Y g))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionFixedTriangle X Y Z p := by
    rw [targetTriangle, prism_parameter, ← Category.assoc, prismEdge_target]
    rw [SpectrumMappingAcyclic.homEquiv'_eq_vertex]
  apply SSet.yonedaEquiv.injective
  exact ((congrArg SSet.yonedaEquiv he).trans
    (coherentCompositionFixedTriangle_vertex _ _)).trans
      (SSet.yonedaEquiv.apply_symm_apply _).symm

end SerrePositivity.KST.LocalizingInvariants.SpectrumPostcomposition
