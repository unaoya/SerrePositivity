module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomOrdinary

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass
public import SerrePositivity.KST.Spectra.SpectrumMappingComponents
public import SerrePositivity.KST.Spectra.ComponentHomotopyMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatFunctorCoreIso

/-!
概要：Sp のホモトピー圏で同じ射は、全整数次数で同じ準同型を誘導する。
方針：coherent Hom 比較の π₀ の単射性を使い、元の BF 写像空間へ戻す。
規約：段ごとの等式を Sp の射の等式の代用にしない。使われ方：K-5 の長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

local instance homotopyClassSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance homotopyClassHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

variable {X Y : OmegaSpectrum.{u}} (f g : X ⟶ Y)

/-- 元の二つの BF 射の辺の類の等式は、実写像空間の成分の等式を与える。 -/
lemma component_eq_of_hom_eq (h : hom f = hom g) :
    SpectrumMappingAcyclic.component f = SpectrumMappingAcyclic.component g := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
      (c.app _ (ULift.up (SimplicialCategory.homEquiv' X Y f))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated :=
    SSet.Truncated.Edge.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary f)
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
      (c.app _ (ULift.up (SimplicialCategory.homEquiv' X Y g))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).toTruncated :=
    SSet.Truncated.Edge.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary g)
  have hp : mapπ₀ c (π₀.mk (ULift.up (SimplicialCategory.homEquiv' X Y f))) =
      mapπ₀ c (π₀.mk (ULift.up (SimplicialCategory.homEquiv' X Y g))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)
    change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _ _) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _ _)
    rw [hf, hg]
    exact h
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isSimplicialHomotopyEquivalence X Y).mapPiZero_bijective
  have hc := hb.injective hp
  have hd := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentUliftPiZeroDown (SimplicialCategory.sHom X Y)) hc
  have hv (a : X ⟶ Y) : SimplicialCategory.homEquiv' X Y a = vertexOfHom a := by
    change (SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (vertexOfHom a)) = vertexOfHom a
    exact Equiv.apply_symm_apply _ _
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentUliftPiZeroDown, π₀.lift_mk, SpectrumMappingAcyclic.component,
    hv] using hd

/-- 整数 π の作用は、Sp のホモトピー圏の射のみに依存する。 -/
lemma homotopyMap_eq_of_hom_eq (h : hom f = hom g) (j : ℤ) :
    homotopyMap f j = homotopyMap g j := by
  apply homotopyMap_eq_of_levelComponent f g _ j
  intro n
  have hc := congrArg (mapπ₀ (evaluation X Y n)) (component_eq_of_hom_eq f g h)
  simpa only [SpectrumMappingAcyclic.component, mapπ₀_mk, vertexOfHom_evaluation,
    PointedMapping.componentOf, PointedMapping.familyVertex_eq_pointedHomVertex] using hc

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
