module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexShiftHomologyCycles

/-!
概要：連続 shift 間の次数一作用素のホモロジー射を元の鎖写像へ比較する。
方針：指定次数の実成分の可換性を cycle 上へ持ち上げる。
規約：成分の次数輸送を明示し、同型の自然性を仮定しない。
使われ方：符号つき一次ブロックと元の面・辺のホモロジー射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R]

lemma dgDegreeOneHomologyMap_shift {K L : Complex R} (f : K ⟶ L)
    (n q r : ℤ) (hr : (n + 1) + q = r)
    (z : Cochain (K⟦n + 1⟧) (L⟦n⟧) 1) (hz : δ 1 2 z = 0)
    (h : z.v q (q + 1) rfl ≫ (L.shiftFunctorObjXIso n (q + 1) r (by omega)).hom =
      (K.shiftFunctorObjXIso (n + 1) q r (by omega)).hom ≫ f.f r) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z hz q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R L n (q + 1) r (by omega)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R K (n + 1) q r hr).hom ≫ HomologicalComplex.homologyMap f r := by
  have hc : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R z hz q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftCyclesIso R L n (q + 1) r (by omega)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftCyclesIso R K (n + 1) q r hr).hom ≫ HomologicalComplex.cyclesMap f r := by
    rw [← cancel_mono (L.iCycles r)]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftCyclesIso_i, HomologicalComplex.cyclesMap_i,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i_assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftCyclesIso_i_assoc]
    rw [h]
  rw [← cancel_epi ((K⟦n + 1⟧).homologyπ q), ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso_cycles,
    ← Category.assoc ((K⟦n + 1⟧).homologyπ q), _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso_cycles,
    Category.assoc, HomologicalComplex.homologyπ_naturality]
  simpa only [Category.assoc] using congrArg (fun a => a ≫ L.homologyπ r) hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
