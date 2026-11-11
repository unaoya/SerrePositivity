module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexCycleElements

/-!
概要：実 cycle のホモロジー類が零であることと実境界であることの同値。
方針：明示した隣接短複体の cycles・opcycles の加群表示を使う。
規約：全整数次数と実微分を保持する。
使われ方：有限 support の primitive を有限段階へ持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R]

lemma dgComplexHomologyClass_sc (K : Complex R) (q : ℤ) (z : K.X q)
    (hz : K.d q (q + 1) z = 0) :
    (K.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass R K q z hz) =
    (K.sc' (q - 1) q (q + 1)).homologyπ
      ((K.sc' (q - 1) q (q + 1)).moduleCatCyclesIso.inv ⟨z, hz⟩) := by
  let c := (K.sc' (q - 1) q (q + 1)).moduleCatCyclesIso.inv ⟨z, hz⟩
  have hc : (K.cyclesIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCycleOfElement R K q z hz) = c := by
    change (K.cyclesIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom
      ((K.cyclesIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).inv c) = c
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  have hp := ConcreteCategory.congr_hom
    (K.π_homologyIsoSc'_hom (q - 1) q (q + 1) (by simp) (by simp))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexCycleOfElement R K q z hz)
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass, ModuleCat.comp_apply, hc] using! hp

lemma dgComplexHomologyClass_eq_zero_iff (K : Complex R) (q : ℤ) (z : K.X q)
    (hz : K.d q (q + 1) z = 0) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass R K q z hz = 0 ↔ ∃ y : K.X (q - 1), K.d (q - 1) q y = z := by
  let S := K.sc' (q - 1) q (q + 1)
  let c := S.moduleCatCyclesIso.inv ⟨z, hz⟩
  have hci : S.iCycles c = z := by
    have h := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles
      (⟨z, hz⟩ : LinearMap.ker (K.d q (q + 1)).hom)
    simpa only [ModuleCat.comp_apply] using! h
  have hπ : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass R K q z hz = 0 ↔ S.homologyπ c = 0 := by
    constructor
    · intro h
      have hh := congrArg (fun a =>
        (K.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom a) h
      rw [dgComplexHomologyClass_sc, map_zero] at hh
      exact hh
    · intro h
      apply (ModuleCat.mono_iff_injective
        (K.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom).mp inferInstance
      rw [dgComplexHomologyClass_sc, h, map_zero]
  have hs : S.homologyπ c = 0 ↔ S.pOpcycles z = 0 := by
    have he := ConcreteCategory.congr_hom S.homology_π_ι c
    have he' : S.homologyι (S.homologyπ c) = S.pOpcycles z := by
      simpa only [ModuleCat.comp_apply, hci] using! he
    constructor
    · intro h
      rw [h, map_zero] at he'
      exact he'.symm
    · intro h
      apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
      rw [he', h, map_zero]
  exact hπ.trans (hs.trans ((S.moduleCat_pOpcycles_eq_zero_iff z).trans Iff.rfl))

lemma dgComplexHomologyClass_boundary_zero (K : Complex R) (q : ℤ) (y : K.X (q - 1))
    (hy : K.d q (q + 1) (K.d (q - 1) q y) = 0) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass R K q (K.d (q - 1) q y) hy = 0 :=
  (dgComplexHomologyClass_eq_zero_iff R K q _ hy).mpr ⟨y, rfl⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
