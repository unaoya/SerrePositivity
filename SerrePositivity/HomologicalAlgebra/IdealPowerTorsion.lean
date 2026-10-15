module
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Ideal-power torsion and Hom from quotient modules -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite
variable {R : Type u} [CommRing R]

/-- The actual submodule of elements killed by some power of an ideal, as a coefficient functor. -/
def idealPowerTorsionFunctor (I : Ideal R) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (I.primaryComponent M)
  map {M N} f := ModuleCat.ofHom
    (Ideal.primaryComponent.map I (M₁ := M) (M₂ := N) f.hom)
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- Ideal-power torsion is additive on actual coefficient morphisms. -/
instance idealPowerTorsionFunctor_additive (I : Ideal R) :
    (idealPowerTorsionFunctor I).Additive where
  map_add := by intro M N f g; ext x; rfl

/-- Ideal-power torsion retains the original linear coefficient action. -/
instance idealPowerTorsionFunctor_linear (I : Ideal R) :
    Functor.Linear R (idealPowerTorsionFunctor I) where
  map_smul := by intro M N f r; ext x; rfl

/-- The torsion submodules include naturally in their original coefficient modules. -/
def idealPowerTorsionInclusion (I : Ideal R) :
    idealPowerTorsionFunctor I ⟶ 𝟭 (ModuleCat.{u} R) where
  app M := ModuleCat.ofHom (I.primaryComponent M).subtype
  naturality {M N} f := by ext x; rfl

/-- Evaluation at one identifies quotient-module Hom with the submodule annihilated by the ideal. -/
def quotientHomEvalOneEquiv (I : Ideal R) (M : ModuleCat.{u} R) :
    (ModuleCat.of R (R ⧸ I) ⟶ M) ≃ₗ[R] Submodule.torsionBySet R M (I : Set R) where
  toFun f := ⟨f 1, by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    rw [← f.hom.map_smul]
    have h : (a : R) • (1 : R ⧸ I) = 0 := by
      simpa only [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] using
        Ideal.Quotient.eq_zero_iff_mem.mpr a.property
    rw [h, map_zero]⟩
  invFun x := ModuleCat.ofHom (I.liftQ (LinearMap.toSpanSingleton R M x.val) (by
    intro a ha
    change a • x.val = 0
    exact (Submodule.mem_torsionBySet_iff _ _).mp x.property ⟨a, ha⟩))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change a • f 1 = f (Ideal.Quotient.mk I a)
    rw [← f.hom.map_smul]
    congr 1
    simp [Algebra.smul_def]
  right_inv x := by
    apply Subtype.ext
    change (I.liftQ (LinearMap.toSpanSingleton R M x.val) _) (1 : R ⧸ I) = x.val
    change (LinearMap.toSpanSingleton R M x.val) (1 : R) = x.val
    exact one_smul R x.val
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; rfl

/-- The inverse quotient-Hom representation sends one to the specified annihilated element. -/
@[simp] lemma quotientHomEvalOneEquiv_symm_apply_one (I : Ideal R) (M : ModuleCat.{u} R)
    (x : Submodule.torsionBySet R M (I : Set R)) :
    (quotientHomEvalOneEquiv I M).symm x 1 = x.val := by
  change (1 : R) • x.val = x.val
  exact one_smul R x.val

end SerrePositivity
