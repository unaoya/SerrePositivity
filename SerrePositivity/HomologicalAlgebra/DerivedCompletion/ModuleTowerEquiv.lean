module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Compatible stage equivalences preserve the actual difference kernels and cokernels -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] {M N : ℕ → Type v}
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n) (s : ∀ n, N (n + 1) →ₗ[R] N n)
  (e : ∀ n, M n ≃ₗ[R] N n)
  (he : ∀ n x, e n (t n x) = s n (e (n + 1) x))

include he in
lemma moduleTowerDifference_equiv (x : ∀ n, M n) :
    (LinearEquiv.piCongrRight e) (moduleTowerDifference R M t x) =
      moduleTowerDifference R N s ((LinearEquiv.piCongrRight e) x) := by
  ext n
  simp only [LinearEquiv.piCongrRight_apply, moduleTowerDifference_apply, map_sub, he]

/-- The map of inverse limits keeps every original component. -/
def moduleTowerLimitEquiv : moduleTowerLimit R M t ≃ₗ[R] moduleTowerLimit R N s where
  toFun x := ⟨(LinearEquiv.piCongrRight e) x.val, by
    change moduleTowerDifference R N s ((LinearEquiv.piCongrRight e) x.val) = 0
    rw [← moduleTowerDifference_equiv R t s e he, show moduleTowerDifference R M t x.val = 0
      from x.property, map_zero]⟩
  invFun y := ⟨(LinearEquiv.piCongrRight e).symm y.val, by
    change moduleTowerDifference R M t ((LinearEquiv.piCongrRight e).symm y.val) = 0
    apply (LinearEquiv.piCongrRight e).injective
    rw [moduleTowerDifference_equiv R t s e he, LinearEquiv.apply_symm_apply, map_zero]
    exact y.property⟩
  left_inv x := Subtype.ext ((LinearEquiv.piCongrRight e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((LinearEquiv.piCongrRight e).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((LinearEquiv.piCongrRight e).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((LinearEquiv.piCongrRight e).map_smul r x.val)

@[simp] lemma moduleTowerLimitEquiv_apply (x : moduleTowerLimit R M t) (n : ℕ) :
    (moduleTowerLimitEquiv R t s e he x).val n = e n (x.val n) := rfl

include he in
lemma moduleTowerDifference_range_equiv :
    (moduleTowerDifference R M t).range.map (LinearEquiv.piCongrRight e).toLinearMap =
      (moduleTowerDifference R N s).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(LinearEquiv.piCongrRight e) x, (moduleTowerDifference_equiv R t s e he x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨moduleTowerDifference R M t ((LinearEquiv.piCongrRight e).symm x),
      ⟨_, rfl⟩, ?_⟩
    change (LinearEquiv.piCongrRight e)
      (moduleTowerDifference R M t ((LinearEquiv.piCongrRight e).symm x)) = _
    rw [moduleTowerDifference_equiv R t s e he, LinearEquiv.apply_symm_apply]

/-- The original difference cokernel, retaining rather than discarding lim¹. -/
def moduleTowerLimOneEquiv :
    ((∀ n, M n) ⧸ (moduleTowerDifference R M t).range) ≃ₗ[R]
      ((∀ n, N n) ⧸ (moduleTowerDifference R N s).range) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.piCongrRight e)
    (moduleTowerDifference_range_equiv R t s e he)

@[simp] lemma moduleTowerLimOneEquiv_mk (x : ∀ n, M n) :
    moduleTowerLimOneEquiv R t s e he (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((LinearEquiv.piCongrRight e) x) := rfl

section Restrict
open CategoryTheory
variable {S : Type u} [CommRing S] [Algebra R S]
  (P : ℕ → ModuleCat.{u} S) (v : ∀ n, P (n + 1) ⟶ P n)

/-- Coefficient restriction preserves the original compatible sequences. -/
def moduleTowerLimitRestrictScalarsEquiv :
    moduleTowerLimit R
      (fun n => (ModuleCat.restrictScalars (algebraMap R S)).obj (P n))
      (fun n => ((ModuleCat.restrictScalars (algebraMap R S)).map (v n)).hom) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S (moduleTowerLimit S (fun n => P n) (fun n => (v n).hom))) where
  toFun x := ⟨x.val, x.property⟩
  invFun y := ⟨y.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficient restriction preserves the actual difference cokernel, including its scalar action. -/
def moduleTowerLimOneRestrictScalarsEquiv :
    ((∀ n, (ModuleCat.restrictScalars (algebraMap R S)).obj (P n)) ⧸
      (moduleTowerDifference R
        (fun n => (ModuleCat.restrictScalars (algebraMap R S)).obj (P n))
        (fun n => ((ModuleCat.restrictScalars (algebraMap R S)).map (v n)).hom)).range) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S ((∀ n, P n) ⧸
          (moduleTowerDifference S (fun n => P n) (fun n => (v n).hom)).range)) := by
  letI : ∀ n, Module R (P n) := fun n => Module.compHom (P n) (algebraMap R S)
  letI : IsScalarTower R S (∀ n, P n) := IsScalarTower.of_algebraMap_smul fun r x => rfl
  exact Submodule.Quotient.restrictScalarsEquiv R
    (moduleTowerDifference S (fun n => P n) (fun n => (v n).hom)).range

end Restrict
end SerrePositivity.DerivedCompletion
