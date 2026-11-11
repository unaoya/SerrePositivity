module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedConnectiveSquare
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison
public import SerrePositivity.KST.SConstruction.KSpectrumInvariance

/-!
概要：同じ実小核の Perf 比較を使い、元の固定 K から実平坦懸垂の native loop へ送る。
方針：元の SOA 比較と指定 Perf 同値を、ν 認証のない同じ実四角形の構造射へ前合成する。
規約：指定 Perf 同値・零所属・実零角の Perf 零性に条件付き。P 照合の存在は主張しない。
使われ方：K-7 c5 の一般経路。構造射の非負次数の安定化を同じ実 fiber 比較へ戻す。
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
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance resolvedConnectiveMapSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance resolvedConnectiveMapSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (e : StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
    (stableCategoryModel (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))))

/-- 指定 Perf 同値に条件付きの、元の固定 K から D-9 の同じ実核 K への実 BF 射。 -/
def dgKappaResolvedKernelKComparison :
    dgKInputSpectrum R D ⟶ dgKInputSpectrum R (dgKappaResolvedKernelKInput R D I) :=
  presentedPerfectDGBFSOAInverseComparison R D ≫ kSpectrumMap e.hom ≫
    presentedPerfectDGBFSOASpectrumComparison R (dgKappaResolvedKernelKInput R D I)

set_option maxHeartbeats 800000 in
/-- 指定 Perf 同値に条件付きで、元の実核比較は全整数 π 同型。ν の Verdier 認証は使わない。 -/
theorem dgKappaResolvedKernelKComparison_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaResolvedKernelKComparison R D I e) :=
  (presentedPerfectDGBFSOAInverseComparison_piIsomorphism R D).comp
    ((kSpectrumMap_piIsomorphism_of_equivalence e).comp
      (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R (dgKappaResolvedKernelKInput R D I)))

variable (Z : DGKappaZeroInput R D I)
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R
    (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))))

/-- 指定 Perf 同値・零所属・実零角に条件付きの、同じ実核からの構造射。 -/
def dgKappaResolvedKernelStructureMap :=
  dgKappaSuspensionConnectiveStructureMap R D I Z (dgKappaResolvedConnectiveSquare R D I)
    (dgKappaResolvedConnectiveSquare_zero_corner R D I hz)
    (dgKappaResolvedConnectiveSquare_vertices R D I).2.1
    (dgKappaResolvedConnectiveSquare_vertices R D I).2.2.1
    (dgKappaResolvedKernelKInput R D I) (dgKappaResolvedConnectiveSquare_vertices R D I).1

/-- 指定 Perf 同値・零所属・実零角に条件付きの、元の K(D) 始点の同じ実構造射。 -/
def dgKappaResolvedConnectiveStructureMap :
    dgKInputSpectrum R D ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)))) :=
  dgKappaResolvedKernelKComparison R D I e ≫ dgKappaResolvedKernelStructureMap R D I Z hz

/-- 明示比較・零所属・実零角に条件付きで、元の K(D) 始点への移送は指定次数の全単射性を保つ。 -/
theorem dgKappaResolvedConnectiveStructureMap_bijective_iff (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaResolvedConnectiveStructureMap R D I e Z hz) j) ↔
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaResolvedKernelStructureMap R D I Z hz) j) := by
  rw [dgKappaResolvedConnectiveStructureMap, OmegaSpectrum.homotopyMap_comp]
  exact Function.Bijective.of_comp_iff _ (dgKappaResolvedKernelKComparison_piIsomorphism R D I e j)

end SerrePositivity.KST.NonConnective
