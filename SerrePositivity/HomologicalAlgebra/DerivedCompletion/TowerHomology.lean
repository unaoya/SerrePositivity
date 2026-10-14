module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ProductHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # ホモトピー逆極限のホモロジーとMilnor列

差分写像の錐の長完全列を、成分ホモロジーの直積の差分へ移す。
負次数の差分の余核を保持し、通常の逆極限と無条件に同一視しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

private theorem shortComplexZero {S : ShortComplex (ModuleCat.{u} R)} (_h : S.Exact) :
    S.f ≫ S.g = 0 := S.zero

/-- 各次数のホモロジーの直積上の差分写像。 -/
def complexTowerHomologyDifference (i : ℤ) :
    (∀ n, (K n).homology i) →ₗ[R] (∀ n, (K n).homology i) :=
  moduleTowerDifference R (fun n ↦ (K n).homology i)
    (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom)

/-- 候補複体のホモロジーを、差分写像の錐の一つ下の次数へ同定する。 -/
def complexTowerHomologyShiftEquiv (i : ℤ) :
    (complexTowerHomotopyLimit R K t).homology i ≃ₗ[R]
      (CochainComplex.mappingCone (complexTowerDifference R K t)).homology (i - 1) :=
  ((CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-1) i (i - 1)
    (by omega)).app (CochainComplex.mappingCone (complexTowerDifference R K t))).toLinearEquiv

/-- 錐の包含による、前の次数のホモロジー直積からの写像。 -/
def complexTowerHomologyIncoming (i : ℤ) :
    (∀ n, (K n).homology (i - 1)) →ₗ[R]
      (complexTowerHomotopyLimit R K t).homology i :=
  (complexTowerHomologyShiftEquiv R K t i).symm.toLinearMap.comp
    ((HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (complexTowerDifference R K t)) (i - 1)).hom.comp
        (complexProductHomologyEquiv R K (i - 1)).symm.toLinearMap)

/-- 錐の連結射による、同じ次数のホモロジー直積への写像。 -/
def complexTowerHomologyBoundary (i : ℤ) :
    (complexTowerHomotopyLimit R K t).homology i →ₗ[R] ∀ n, (K n).homology i :=
  (complexProductHomologyEquiv R K i).toLinearMap.comp
    ((Cone.δ (complexTowerDifference R K t) (i - 1) i (by omega)).hom.comp
      (complexTowerHomologyShiftEquiv R K t i).toLinearMap)

/-- 包含に誘導される写像の核は、前の次数の差分の像。 -/
theorem complexTowerHomologyIncoming_zero_iff (i : ℤ)
    (y : ∀ n, (K n).homology (i - 1)) :
    complexTowerHomologyIncoming R K t i y = 0 ↔
      ∃ z, complexTowerHomologyDifference R K t (i - 1) z = y := by
  let φ := complexTowerDifference R K t
  have hE := (ShortComplex.moduleCat_exact_iff _).mp (Cone.exact₂ φ (i - 1))
  constructor
  · intro hy
    have hy' : HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) (i - 1)
        ((complexProductHomologyEquiv R K (i - 1)).symm y) = 0 := by
      have h := congrArg (complexTowerHomologyShiftEquiv R K t i) hy
      simpa [complexTowerHomologyIncoming] using h
    obtain ⟨z, hz⟩ := hE _ hy'
    refine ⟨complexProductHomologyEquiv R K (i - 1) z, ?_⟩
    simp only [complexTowerHomologyDifference]
    rw [← complexProductHomologyEquiv_difference]
    exact (congrArg (complexProductHomologyEquiv R K (i - 1)) hz).trans
      ((complexProductHomologyEquiv R K (i - 1)).apply_symm_apply y)
  · rintro ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (complexProductHomologyEquiv R K (i - 1)).surjective z
    simp only [complexTowerHomologyDifference]
    rw [← complexProductHomologyEquiv_difference]
    simp only [complexTowerHomologyIncoming, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have h := congrArg (fun f ↦ f.hom z)
      (shortComplexZero R (Cone.exact₂ φ (i - 1)))
    simpa using congrArg (complexTowerHomologyShiftEquiv R K t i).symm h

/-- 連結射の核は、前の次数の包含の像。 -/
theorem complexTowerHomologyBoundary_zero_iff (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyBoundary R K t i x = 0 ↔
      ∃ y, complexTowerHomologyIncoming R K t i y = x := by
  let φ := complexTowerDifference R K t
  have hE := Cone.exact₃ φ (i - 1) i (by omega)
  constructor
  · intro hx
    have hx' : Cone.δ φ (i - 1) i (by omega)
        (complexTowerHomologyShiftEquiv R K t i x) = 0 := by
      apply (complexProductHomologyEquiv R K i).injective
      simpa [complexTowerHomologyBoundary] using hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hE _ hx'
    refine ⟨complexProductHomologyEquiv R K (i - 1) y, ?_⟩
    simp only [complexTowerHomologyIncoming, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (complexTowerHomologyShiftEquiv R K t i).symm_apply_eq.mpr hy
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f ↦ f.hom ((complexProductHomologyEquiv R K (i - 1)).symm y))
      (shortComplexZero R hE)
    simpa [complexTowerHomologyBoundary, complexTowerHomologyIncoming] using
      congrArg (complexProductHomologyEquiv R K i) h

/-- 連結射の像は、同じ次数の差分の核。 -/
theorem complexTowerHomologyBoundary_range (i : ℤ) :
    (complexTowerHomologyBoundary R K t i).range =
      (complexTowerHomologyDifference R K t i).ker := by
  let φ := complexTowerDifference R K t
  have hE := Cone.exact₁ φ (i - 1) i (by omega)
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change complexTowerHomologyDifference R K t i
      (complexTowerHomologyBoundary R K t i x) = 0
    rw [complexTowerHomologyBoundary, LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [complexTowerHomologyDifference]
    have h := congrArg (fun f ↦ f.hom (complexTowerHomologyShiftEquiv R K t i x))
      (shortComplexZero R hE)
    exact (complexProductHomologyEquiv_difference R K t i _).symm.trans
      ((congrArg (complexProductHomologyEquiv R K i) h).trans (map_zero _))
  · intro hy
    have hy' : HomologicalComplex.homologyMap φ i
        ((complexProductHomologyEquiv R K i).symm y) = 0 := by
      apply (complexProductHomologyEquiv R K i).injective
      rw [complexProductHomologyEquiv_difference, LinearEquiv.apply_symm_apply, map_zero]
      exact hy
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hE _ hy'
    refine ⟨(complexTowerHomologyShiftEquiv R K t i).symm x, ?_⟩
    simp only [complexTowerHomologyBoundary, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (congrArg (complexProductHomologyEquiv R K i) hx).trans
      ((complexProductHomologyEquiv R K i).apply_symm_apply y)

end SerrePositivity.DerivedCompletion
