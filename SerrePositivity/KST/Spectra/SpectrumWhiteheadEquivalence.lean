module

public import SerrePositivity.KST.Spectra.SpectrumMappingComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EnrichedHomotopy

/-!
概要：段ごとの全基点 π 同型の BF 射は、本レーンの Sp の同値を与える。
方針：全豊穣 Hom の π₀ における両側の逆を、Kan な Hom の頂点同型へ戻し γ3 へ渡す。
規約：元の BF 射そのものの coherent な辺の可逆性を証明する。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。置換と ∞ 極限・安定性の合流。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{u}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y
open OmegaSpectrum

/-- 単体的圏の零単体の表示は既存の厳密射の頂点と一致する。 -/
lemma homEquiv'_eq_vertex {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    SimplicialCategory.homEquiv' X Y f = vertexOfHom f := by
  change (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm (vertexOfHom f)) = _
  exact Equiv.apply_symm_apply _ _

/-- 全写像空間の成分の等式から、豊穣 Hom 内の実際の頂点同型を得る。 -/
def vertexIsoOfComponentEq {X Y : OmegaSpectrum.{u}} {f g : X ⟶ Y}
    (h : component f = component g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (SimplicialCategory.homEquiv' X Y f) (SimplicialCategory.homEquiv' X Y g) := by
  rw [homEquiv'_eq_vertex, homEquiv'_eq_vertex]
  let e := Classical.choice (nonempty_edge_of_piZero_eq h)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (mappingSpace X Y)) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)

/-- BF 射の各段の全基点 π 同型は、Sp の実際の同値を与える。 -/
theorem isInvertible_of_levelwise {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) := by
  obtain ⟨g, hg, hh⟩ := exists_componentInverse f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse f g
    (vertexIsoOfComponentEq hg) (vertexIsoOfComponentEq hh)

end
end SerrePositivity.KST.Spectra.SpectrumMappingAcyclic
