module
public import SerrePositivity.KST.NonConnective.DGKappaSplitCofiberSupply
public import SerrePositivity.KST.NonConnective.DGSuspensionIteration
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFQuasiEquivalence

/-!
概要：同じ実平坦 dg 懸垂の屋根を、固定 dg K の厳密な二脚として保持する。
方針：cell 分解の増大と元の商包含を固定入力射にし、同じ増大の K 像を可逆化する。
規約：元の cone から商への厳密 dg 射を捏造せず、同じ平坦分解の屋根を使う。
使われ方：反復懸垂の構造射と、その元の入力に関する整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance suspensionRoofSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance suspensionRoofSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の同じ cone の具体的 cell 分解を、固定 dg K の入力に保持する。 -/
def dgKappaResolvedConeKInput : PerfDGInput R :=
  perfDGInputOf R (DGCategoryCellResolution.Source R (DGKappaCone R D I))

/-- 懸垂屋根の左脚は、同じ cell 分解の元の厳密な増大。 -/
def dgKappaResolvedConeAugmentationInputMap :
    dgKappaResolvedConeKInput R D I ⟶ dgKappaConeKInput R D I :=
  ULift.up (DGCategoryCellResolution.augmentation R (DGKappaCone R D I))

/-- 懸垂屋根の右脚は、同じ分解上の同じ対象集合を零化する元の厳密 dg 商包含。 -/
def dgKappaResolvedSuspensionInputMap :
    dgKappaResolvedConeKInput R D I ⟶ dgKappaSuspensionKInput R D I :=
  ULift.up (DGQuotient.inclusion R (DGCategoryCellResolution.Source R (DGKappaCone R D I))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)))

/-- 左脚の同じ固定 K 像は、全整数群で同型を誘導する。 -/
theorem dgKappaResolvedConeAugmentation_piIsomorphism :
    OmegaSpectrum.PiIsomorphism
      (dgKInputSpectrumMap R (dgKappaResolvedConeAugmentationInputMap R D I)) :=
  presentedPerfectDGBFMap_piIsomorphism_of_quasiEquivalence R _
    (DGCategoryCellResolution.augmentation_quasiEquivalence R (DGKappaCone R D I))

/-- 元の増大の固定 K 像の実辺そのものが Sp 内で可逆。 -/
theorem dgKappaResolvedConeAugmentation_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (dgKInputSpectrumMap R (dgKappaResolvedConeAugmentationInputMap R D I))) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgKappaResolvedConeAugmentation_piIsomorphism R D I)

/-- 同じ実増大による、平坦 cone と元の cone の固定 K 頂点間の実同型。 -/
def dgKappaResolvedConeKVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaResolvedConeKInput R D I)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaConeKInput R D I))) := by
  have : IsIso (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap R
        (dgKappaResolvedConeAugmentationInputMap R D I))).toTruncated) :=
    dgKappaResolvedConeAugmentation_isInvertible R D I
  exact asIso (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap R (dgKappaResolvedConeAugmentationInputMap R D I))).toTruncated)

/-- 元の同じ平坦 cone の固定 K も、同じ増大を介して実 Sp の零頂点。 -/
theorem dgKappaResolvedConeK_isZeroVertex (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaResolvedConeKInput R D I))) :=
  (dgKappaFixedK_isZeroVertex R D I Z).of_vertexIso (dgKappaResolvedConeKVertexIso R D I).symm

end SerrePositivity.KST.NonConnective
