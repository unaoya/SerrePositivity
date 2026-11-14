module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedNullPerf
public import SerrePositivity.KST.NonConnective.DGKappaResolvedConnectiveMap

/-!
概要：元の実 fiber 比較の非負次数条件を、同じ固定 K の実懸垂構造射へ移送する。
方針：同じ比較辺の頂点座標の移送だけを消去し、native loop 比較と Perf 同値の全単射性を使う。
規約：指定 Perf 同値と零所属に条件付き。零角は実供給し、Sp 引き戻し性や ν の Verdier 証拠は使わない。
使われ方：連結版 K-6 d を K-7 c5・d の元の各段へ適用する界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.Fibration SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance connectivePiSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

private theorem fiberPi_bijective_ofEq {x y x' y' : Sp.{w} _⦋0⦌}
    (f : Sp.{w}.Edge x y) (hx : x = x') (hy : y = y') (j : ℤ) :
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk (f.ofEq hx hy).toTruncated) j) ↔
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk f.toTruncated) j) := by
  cases hx
  cases hy
  rfl

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (Z : DGKappaZeroInput R D I)
  (F : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R)
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (F ≫ dgKInputK R) 0 1))
  (hMiddle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaResolvedConeKInput R D I))
  (hRight : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R D I))
  (A : PerfDGInput.{u, max (u + 1) v} R)
  (hLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)

/-- 明示四角形・零所属に条件付きで、構造射の全単射性は元の実 fiber 比較そのものと同値。 -/
theorem dgKappaSuspensionConnectiveStructureMap_bijective_iff_fiber (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaSuspensionConnectiveStructureMap R D I Z F hz hMiddle hRight A hLeft) j) ↔
      Function.Bijective (dgConnectiveFiberComparisonPi R F hz j).hom := by
  rw [dgKappaSuspensionConnectiveStructureMap_bijective_iff]
  unfold dgKappaSuspensionConnectiveLoopComparison
  exact fiberPi_bijective_ofEq _ _ _ j

section Original
variable (B : PerfDGInput.{u, max (u + 1) v} R) (J : DGKappaConeInput R B κ)
  (e : StableModelEquivalence (stableCategoryModel (dgKInputStableValue R B))
    (stableCategoryModel (dgKInputStableValue R (dgKappaResolvedKernelKInput R B J))))
  (Z' : DGKappaZeroInput R B J)

/-- 指定 Perf 同値・零所属に条件付きで、元の K(B) 構造射の条件は同じ元の実 fiber 比較。 -/
theorem dgKappaResolvedConnectiveStructureMap_bijective_iff_fiber (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaResolvedConnectiveStructureMap R B J e Z' (dgKappaResolvedNullPerf_isZero R B J)) j) ↔
    Function.Bijective (dgConnectiveFiberComparisonPi R (dgKappaResolvedConnectiveSquare R B J)
      (dgKappaResolvedConnectiveSquare_zero_corner R B J (dgKappaResolvedNullPerf_isZero R B J)) j).hom := by
  apply (dgKappaResolvedConnectiveStructureMap_bijective_iff R B J e Z'
    (dgKappaResolvedNullPerf_isZero R B J) j).trans
  exact dgKappaSuspensionConnectiveStructureMap_bijective_iff_fiber R B J Z'
    (dgKappaResolvedConnectiveSquare R B J)
    (dgKappaResolvedConnectiveSquare_zero_corner R B J (dgKappaResolvedNullPerf_isZero R B J))
    (dgKappaResolvedConnectiveSquare_vertices R B J).2.1
    (dgKappaResolvedConnectiveSquare_vertices R B J).2.2.1
    (dgKappaResolvedKernelKInput R B J) (dgKappaResolvedConnectiveSquare_vertices R B J).1 j

/-- 連結版 fibration の同じ実 fiber 比較に条件付きで、元の実構造射は非負次数 π 同型。 -/
theorem dgKappaResolvedConnectiveStructureMap_nonnegative
    (h : ∀ j : ℤ, 0 ≤ j → Function.Bijective
      (dgConnectiveFiberComparisonPi R (dgKappaResolvedConnectiveSquare R B J)
        (dgKappaResolvedConnectiveSquare_zero_corner R B J (dgKappaResolvedNullPerf_isZero R B J)) j).hom)
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaResolvedConnectiveStructureMap R B J e Z' (dgKappaResolvedNullPerf_isZero R B J)) j) :=
  (dgKappaResolvedConnectiveStructureMap_bijective_iff_fiber R B J e Z' j).mpr (h j hj)

end Original

end SerrePositivity.KST.NonConnective
