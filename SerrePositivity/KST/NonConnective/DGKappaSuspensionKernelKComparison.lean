module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionRelativeRoofInput
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison
public import SerrePositivity.KST.SConstruction.KSpectrumInvariance

/-!
概要：実相対屋根の核を元の Perf へ照合したとき、固定 K の構造比較の始点を戻す。
方針：同じ二つの dg 入力の SOA 比較と、指定 Perf 同値の実 BF 射を合成する。
規約：実相対屋根と指定全関手 Perf 同値に条件付き。その同値の P との照合は K-B の未完工程。
使われ方：K-7 c5。固定 K 入力を保持したまま、元の K(D) から同じ native loop K(Σ) へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance suspensionKernelSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory
local instance suspensionKernelHomKan (X Y : OmegaSpectrum.{w}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (ρ : DGKappaSuspensionRelativeRoofInput R D I)
  (e : StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
    (stableCategoryModel (dgKInputStableValue R ρ.kernel)))

/-- 明示屋根と指定 Perf 同値に条件付きの、元の固定 K から同じ実核 K への実 BF 比較。 -/
def dgKappaSuspensionKernelKComparison :
    dgKInputSpectrum R D ⟶ dgKInputSpectrum R ρ.kernel :=
  presentedPerfectDGBFSOAInverseComparison R D ≫ kSpectrumMap e.hom ≫
    presentedPerfectDGBFSOASpectrumComparison R ρ.kernel

set_option maxHeartbeats 800000 in
-- 同じ fixed K と stableCategoryModel の表示を kernel 内でも照合する。
/-- 明示屋根と指定 Perf 同値に条件付きで、同じ実 BF 比較は全整数次数で π 同型。 -/
theorem dgKappaSuspensionKernelKComparison_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaSuspensionKernelKComparison R D I ρ e) :=
  (presentedPerfectDGBFSOAInverseComparison_piIsomorphism R D).comp
    ((kSpectrumMap_piIsomorphism_of_equivalence e).comp
      (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R ρ.kernel))

/-- 明示屋根と指定 Perf 同値に条件付きで、同じ実比較辺は Sp で可逆。 -/
theorem dgKappaSuspensionKernelKComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionKernelKComparison R D I ρ e)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgKappaSuspensionKernelKComparison_piIsomorphism R D I ρ e)

variable (Z : DGKappaZeroInput R D I)

/-- 明示屋根と指定 Perf 同値に条件付きで、元の固定 K(D) から同じ native loop K(Σ) への実射。 -/
def dgKappaSuspensionOriginalStructureMap :
    dgKInputSpectrum R D ⟶ dgKappaSuspensionNativeLoopSpectrum R D I :=
  dgKappaSuspensionKernelKComparison R D I ρ e ≫ ρ.nativeStructureBFMap R D I Z

/-- 明示屋根と指定 Perf 同値に条件付きで、元の核比較と構造射を保持する同じ実合成二胞体。 -/
def dgKappaSuspensionOriginalStructureTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgKappaSuspensionKernelKComparison R D I ρ e)
    (ρ.nativeStructureBFMap R D I Z)

end SerrePositivity.KST.NonConnective
