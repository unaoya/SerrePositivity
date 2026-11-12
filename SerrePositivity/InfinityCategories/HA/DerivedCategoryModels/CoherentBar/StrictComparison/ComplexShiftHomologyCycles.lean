module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneCyclesMap
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
概要：整数 shift のホモロジー同型と実 cycle の次数輸送。
方針：shift の隣接短複体同型へ cycle とホモロジー関手を適用する。
規約：Mathlib の同じ shift ホモロジー同型を使う。
使われ方：一次層作用素のホモロジー係数の shift 輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (K : Complex R) (n q r : ℤ) (h : n + q = r)

def dgComplexShiftHomologyIso : (K⟦n⟧).homology q ≅ K.homology r :=
  (CochainComplex.ShiftSequence.shiftIso (ModuleCat R) n q r h).app K

def dgComplexShiftCyclesIso : (K⟦n⟧).cycles q ≅ K.cycles r :=
  ShortComplex.cyclesMapIso ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat R) n q r h).app K)

@[reassoc]
lemma dgComplexShiftCyclesIso_i :
    (dgComplexShiftCyclesIso R K n q r h).hom ≫ K.iCycles r =
      (K⟦n⟧).iCycles q ≫ (K.shiftFunctorObjXIso n q r (by omega)).hom := by
  change ShortComplex.cyclesMap _ ≫ (K.sc r).iCycles = _
  rw [ShortComplex.cyclesMap_i]
  rfl

@[reassoc]
lemma dgComplexShiftHomologyIso_cycles :
    (K⟦n⟧).homologyπ q ≫ (dgComplexShiftHomologyIso R K n q r h).hom =
      (dgComplexShiftCyclesIso R K n q r h).hom ≫ K.homologyπ r := by
  change ((K⟦n⟧).sc q).homologyπ ≫ _ = _
  simp only [dgComplexShiftHomologyIso, Iso.app_hom,
    CochainComplex.ShiftSequence.shiftIso_hom_app]
  exact ShortComplex.homologyπ_naturality _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
