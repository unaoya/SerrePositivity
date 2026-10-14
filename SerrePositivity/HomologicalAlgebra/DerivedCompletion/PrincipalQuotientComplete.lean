module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # 主イデアル商の導来完備性

商の導来完備性には生成元の正則性を要しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 主イデアルは生成元の乗法写像の像。 -/
theorem mulLeft_range_eq_span (d : R) :
    (LinearMap.mulLeft R d).range = (Ideal.span {d} : Submodule R R) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Ideal.mem_span_singleton, dvd_def]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩

/-- 主イデアル商を元の環の加群と見た導来完備性。 -/
theorem isModuleComplete_principal_quotient_restrict (f d : R)
    (hR : IsModuleComplete R f (ModuleCat.of R R)) :
    IsModuleComplete R f (ModuleCat.of R (R ⧸ Ideal.span {d})) := by
  have h := isModuleComplete_coker R f (LinearMap.mulLeft R d) hR hR
  rw [mulLeft_range_eq_span] at h
  exact h

/-- 主イデアル商自身の環作用に関する導来完備性。 -/
theorem isModuleComplete_principal_quotient (f d : R)
    (hR : IsModuleComplete R f (ModuleCat.of R R)) :
    IsModuleComplete (R ⧸ Ideal.span {d}) (Ideal.Quotient.mk (Ideal.span {d}) f)
      (ModuleCat.of (R ⧸ Ideal.span {d}) (R ⧸ Ideal.span {d})) := by
  exact (isModuleComplete_algebraMap_iff R (R ⧸ Ideal.span {d}) f
    (R ⧸ Ideal.span {d})).mpr (isModuleComplete_principal_quotient_restrict R f d hR)

/-- pの自然数像を使う公開形。 -/
theorem isModuleComplete_principal_quotient_natCast (p : ℕ) (d : R)
    (hR : IsModuleComplete R (p : R) (ModuleCat.of R R)) :
    IsModuleComplete (R ⧸ Ideal.span {d}) (p : R ⧸ Ideal.span {d})
      (ModuleCat.of (R ⧸ Ideal.span {d}) (R ⧸ Ideal.span {d})) := by
  simpa only [map_natCast] using isModuleComplete_principal_quotient R (p : R) d hR

end SerrePositivity.DerivedCompletion
