module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyClass
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EnrichedHomotopy

/-!
概要：元の BF 写像空間の成分の等式を h Sp の射の等式へ移す。
方針：Kan な実 Hom の連結成分を頂点同型に戻し、coherent nerve の比較を使う。
規約：段ごとの成分の一致とは区別する。使われ方：積の単位則の実際の h Sp での検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance componentClassSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance componentClassHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

lemma hom_eq_of_component_eq {X Y : OmegaSpectrum.{u}} (f g : X ⟶ Y)
    (h : SpectrumMappingAcyclic.component f = SpectrumMappingAcyclic.component g) :
    hom f = hom g := by
  have hv (a : X ⟶ Y) : SimplicialCategory.homEquiv' X Y a = vertexOfHom a := by
    change (SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (vertexOfHom a)) = vertexOfHom a
    exact Equiv.apply_symm_apply _ _
  have hp : π₀.mk (SimplicialCategory.homEquiv' X Y f) =
      π₀.mk (SimplicialCategory.homEquiv' X Y g) := by
    rw [hv, hv]
    exact h
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertexIso_of_piZero_eq hp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_homMk_eq_of_enrichedVertexIso e

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
