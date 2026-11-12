module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyCoordinates
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：加群複体の実 cycle 元からホモロジー類を作り、全類の代表元と自然性を公開する。
方針：明示した隣接短複体の核同型を使う。
規約：非有界の全整数次数を扱う。
使われ方：有限 support による実フィルトレーションの下降と収束。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R]

def dgComplexCycleOfElement (K : Complex R) (q : ℤ) (z : K.X q)
    (hz : K.d q (q + 1) z = 0) : K.cycles q :=
  (K.cyclesIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).inv
    ((K.sc' (q - 1) q (q + 1)).moduleCatCyclesIso.inv ⟨z, hz⟩)

lemma dgComplexCycleOfElement_i (K : Complex R) (q : ℤ) (z : K.X q)
    (hz : K.d q (q + 1) z = 0) : K.iCycles q (dgComplexCycleOfElement R K q z hz) = z := by
  dsimp only [dgComplexCycleOfElement]
  rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  have h := ConcreteCategory.congr_hom
    (K.sc' (q - 1) q (q + 1)).moduleCatCyclesIso_inv_iCycles (⟨z, hz⟩ :
      LinearMap.ker (K.d q (q + 1)).hom)
  simpa only [ModuleCat.comp_apply] using! h

def dgComplexHomologyClass (K : Complex R) (q : ℤ) (z : K.X q)
    (hz : K.d q (q + 1) z = 0) : K.homology q :=
  K.homologyπ q (dgComplexCycleOfElement R K q z hz)

lemma dgComplexHomologyClass_map {K L : Complex R} (f : K ⟶ L) (q : ℤ) (z : K.X q)
    (hz : K.d q (q + 1) z = 0) (hz' : L.d q (q + 1) (f.f q z) = 0) :
    HomologicalComplex.homologyMap f q (dgComplexHomologyClass R K q z hz) =
      dgComplexHomologyClass R L q (f.f q z) hz' := by
  have hc : HomologicalComplex.cyclesMap f q (dgComplexCycleOfElement R K q z hz) =
      dgComplexCycleOfElement R L q (f.f q z) hz' := by
    apply (ModuleCat.mono_iff_injective (L.iCycles q)).mp inferInstance
    rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply,
      dgComplexCycleOfElement_i, dgComplexCycleOfElement_i]
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f q)
    (dgComplexCycleOfElement R K q z hz)
  simpa only [dgComplexHomologyClass, ModuleCat.comp_apply, hc] using! h

lemma dgComplexHomologyClass_surjective (K : Complex R) (q : ℤ) (a : K.homology q) :
    ∃ (z : K.X q) (hz : K.d q (q + 1) z = 0), dgComplexHomologyClass R K q z hz = a := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance a
  let z := K.iCycles q c
  have hz : K.d q (q + 1) z = 0 := ConcreteCategory.congr_hom (K.iCycles_d q (q + 1)) c
  refine ⟨z, hz, congrArg (fun t => K.homologyπ q t) ?_⟩
  apply (ModuleCat.mono_iff_injective (K.iCycles q)).mp inferInstance
  rw [dgComplexCycleOfElement_i]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
