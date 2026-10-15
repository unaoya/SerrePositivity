module

public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Algebra.Defs

/-! # Rings of sections of commutative monoid objects in preadditive monoidal categories -/

@[expose] public noncomputable section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory Opposite
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The existing unit coyoneda tensorator respects the braiding. -/
theorem unitCoyoneda_braiding (X Y : C) :
    Functor.LaxMonoidal.μ (coyoneda.obj (op (𝟙_ C))) X Y ≫
        (coyoneda.obj (op (𝟙_ C))).map (β_ X Y).hom =
      (β_ ((coyoneda.obj (op (𝟙_ C))).obj X)
        ((coyoneda.obj (op (𝟙_ C))).obj Y)).hom ≫
        Functor.LaxMonoidal.μ (coyoneda.obj (op (𝟙_ C))) Y X := by
  ext ⟨f, g⟩
  change ((λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g)) ≫ (β_ X Y).hom =
    (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ f)
  rw [Category.assoc, BraidedCategory.braiding_naturality, ← Category.assoc,
    leftUnitor_inv_braiding, unitors_inv_equal]

/-- The unit coyoneda functor also respects the braiding. -/
@[instance_reducible] def unitCoyonedaLaxBraided :
    (coyoneda.obj (op (𝟙_ C))).LaxBraided where
  toLaxMonoidal := inferInstance
  braided := unitCoyoneda_braiding C

/-- Sections of a commutative algebra object have the canonical commutative monoid structure. -/
@[instance_reducible] def commMonUnitHomCommMonoid (A : CommMon C) :
    CommMonoid (𝟙_ C ⟶ A.X) := by
  letI := unitCoyonedaLaxBraided C
  let B := (coyoneda.obj (op (𝟙_ C))).mapCommMon.obj A
  letI := B.mon
  letI := B.comm
  change CommMonoid B.X
  exact CommMonTypeEquivalenceCommMon.commMonCommMonoid B.X

/-- The section product is exactly tensor followed by the actual algebra multiplication. -/
theorem commMonUnitHom_mul (A : CommMon C) (f g : 𝟙_ C ⟶ A.X) :
    letI := commMonUnitHomCommMonoid C A
    f * g = (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ A.mon.mul := by
  exact Category.assoc _ _ _

/-- The section unit is exactly the actual algebra unit. -/
theorem commMonUnitHom_one (A : CommMon C) :
    letI := commMonUnitHomCommMonoid C A
    (1 : 𝟙_ C ⟶ A.X) = A.mon.one := by
  change 𝟙 (𝟙_ C) ≫ A.mon.one = A.mon.one
  exact Category.id_comp _

variable [Preadditive C] [MonoidalPreadditive C]

/-- The canonical section product is distributive over the existing addition on morphisms. -/
@[instance_reducible] def commMonUnitHomCommRing (A : CommMon C) :
    CommRing (𝟙_ C ⟶ A.X) := by
  letI := commMonUnitHomCommMonoid C A
  exact
    { (inferInstance : AddCommGroup (𝟙_ C ⟶ A.X)),
      (inferInstance : CommMonoid (𝟙_ C ⟶ A.X)) with
      left_distrib := fun f g h ↦ by
        change ((λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ (g + h))) ≫ A.mon.mul = _
        rw [MonoidalPreadditive.tensor_add]
        simp only [Preadditive.comp_add, Preadditive.add_comp]
        rfl
      right_distrib := fun f g h ↦ by
        change ((λ_ (𝟙_ C)).inv ≫ ((f + g) ⊗ₘ h)) ≫ A.mon.mul = _
        rw [MonoidalPreadditive.add_tensor]
        simp only [Preadditive.comp_add, Preadditive.add_comp]
        rfl
      zero_mul := fun f ↦ by
        change ((λ_ (𝟙_ C)).inv ≫ ((0 : 𝟙_ C ⟶ A.X) ⊗ₘ f)) ≫ A.mon.mul = 0
        simp
      mul_zero := fun f ↦ by
        change ((λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ (0 : 𝟙_ C ⟶ A.X))) ≫ A.mon.mul = 0
        simp
      natCast n := n • (1 : 𝟙_ C ⟶ A.X)
      natCast_zero := zero_nsmul _
      natCast_succ n := succ_nsmul _ _
      intCast z := z • (1 : 𝟙_ C ⟶ A.X)
      intCast_ofNat n := by
        change (n : ℤ) • (1 : 𝟙_ C ⟶ A.X) = n • (1 : 𝟙_ C ⟶ A.X)
        simp
      intCast_negSucc n := by
        change Int.negSucc n • (1 : 𝟙_ C ⟶ A.X) = -((n + 1) • (1 : 𝟙_ C ⟶ A.X))
        simp }

/-- Actual algebra morphisms induce ring morphisms on sections by ordinary composition. -/
def commMonUnitHomMap {A B : CommMon C} (f : A ⟶ B) :
    letI := commMonUnitHomCommRing C A
    letI := commMonUnitHomCommRing C B
    (𝟙_ C ⟶ A.X) →+* (𝟙_ C ⟶ B.X) := by
  letI := commMonUnitHomCommRing C A
  letI := commMonUnitHomCommRing C B
  letI := A.mon
  letI := B.mon
  exact
    { toFun := fun g ↦ g ≫ f.hom.hom
      map_zero' := Limits.zero_comp
      map_add' := fun g h ↦ Preadditive.add_comp _ _ _ _ _ _
      map_one' := by
        change (𝟙 (𝟙_ C) ≫ A.mon.one) ≫ f.hom.hom = 𝟙 (𝟙_ C) ≫ B.mon.one
        simp only [Category.id_comp, IsMonHom.one_hom]
      map_mul' := fun g h ↦ by
        change (((λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)) ≫ A.mon.mul) ≫ f.hom.hom =
          ((λ_ (𝟙_ C)).inv ≫ ((g ≫ f.hom.hom) ⊗ₘ (h ≫ f.hom.hom))) ≫ B.mon.mul
        simp only [Category.assoc, IsMonHom.mul_hom]
        have ht : (g ⊗ₘ h) ≫ (f.hom.hom ⊗ₘ f.hom.hom) =
            (g ≫ f.hom.hom) ⊗ₘ (h ≫ f.hom.hom) := tensorHom_comp_tensorHom _ _ _ _
        simpa only [Category.assoc] using
          congrArg (fun k ↦ ((λ_ (𝟙_ C)).inv ≫ k) ≫ B.mon.mul) ht }

variable (R : Type*) [CommRing R] [Linear R C] [MonoidalLinear R C]

omit [MonoidalLinear R C] in
/-- The section product preserves the original scalar action in its first factor. -/
theorem commMonUnitHom_smul_mul (A : CommMon C) (r : R) (f g : 𝟙_ C ⟶ A.X) :
    letI := commMonUnitHomCommRing C A
    (r • f) * g = r • (f * g) := by
  let := commMonUnitHomCommRing C A
  change ((λ_ (𝟙_ C)).inv ≫ ((r • f) ⊗ₘ g)) ≫ A.mon.mul =
    r • (((λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g)) ≫ A.mon.mul)
  simp [tensorHom_def, Linear.smul_comp, Linear.comp_smul]

/-- The section product preserves the original scalar action in its second factor. -/
theorem commMonUnitHom_mul_smul (A : CommMon C) (r : R) (f g : 𝟙_ C ⟶ A.X) :
    letI := commMonUnitHomCommRing C A
    f * (r • g) = r • (f * g) := by
  let := commMonUnitHomCommRing C A
  change ((λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ (r • g))) ≫ A.mon.mul =
    r • (((λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g)) ≫ A.mon.mul)
  simp [tensorHom_def, Linear.smul_comp, Linear.comp_smul]

/-- The resulting algebra structure uses the existing R-module structure on morphisms. -/
@[instance_reducible] def commMonUnitHomAlgebra (A : CommMon C) :
    letI := commMonUnitHomCommRing C A
    Algebra R (𝟙_ C ⟶ A.X) := by
  letI := commMonUnitHomCommRing C A
  exact Algebra.ofModule (commMonUnitHom_smul_mul C R A)
    (commMonUnitHom_mul_smul C R A)

end SerrePositivity
