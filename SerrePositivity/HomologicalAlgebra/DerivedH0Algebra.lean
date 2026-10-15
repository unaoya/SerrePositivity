module

public import SerrePositivity.HomologicalAlgebra.DerivedUnitHomologyNatural
public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBraided
public import SerrePositivity.HomologicalAlgebra.MonoidalUnitHomRing
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Algebra.Hom

/-! # The ring on actual H⁰ of a bounded-above commutative derived algebra -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Transport multiplication along an additive equivalence while retaining source addition. -/
@[instance_reducible] def addEquivCommRingPreservingAdd
    {M N : Type*} [AddCommGroup M] [CommRing N] (e : M ≃+ N) : CommRing M := by
  letI : One M := ⟨e.symm 1⟩
  letI : Mul M := ⟨fun x y ↦ e.symm (e x * e y)⟩
  letI : Pow M ℕ := ⟨fun x n ↦ e.symm (e x ^ n)⟩
  letI : NatCast M := ⟨fun n ↦ e.symm n⟩
  letI : IntCast M := ⟨fun n ↦ e.symm n⟩
  exact e.injective.commRing e e.map_zero (e.apply_symm_apply _) e.map_add
    (fun x y ↦ e.apply_symm_apply _) e.map_neg e.map_sub
    (fun n x ↦ map_nsmul e n x) (fun n x ↦ map_zsmul e n x)
    (fun x n ↦ e.apply_symm_apply _) (fun n ↦ e.apply_symm_apply _)
    (fun n ↦ e.apply_symm_apply _)

/-- The full-subcategory inclusion identifies the two unit Hom modules without changing maps. -/
def boundedAboveUnitHomLinearEquiv (X : D) :
    (𝟙_ D ⟶ X) ≃ₗ[R] (DerivedCategory.Q.obj (cochainTensorUnit (R := R)) ⟶ X.obj) where
  toFun f := f.hom
  invFun f := ObjectProperty.homMk f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual H⁰ module is naturally the unit Hom module in the actual monoidal category. -/
def boundedAboveUnitH0LinearEquiv (X : D) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj ≃ₗ[R] (𝟙_ D ⟶ X) :=
  derivedUnitH0NaturalLinearEquiv R X.obj ≪≫ₗ (boundedAboveUnitHomLinearEquiv X).symm

/-- This comparison uses the actual H⁰ map for every bounded-above derived morphism. -/
theorem boundedAboveUnitH0LinearEquiv_naturality {X Y : D} (f : X ⟶ Y)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj) :
    boundedAboveUnitH0LinearEquiv Y
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom x) =
      boundedAboveUnitH0LinearEquiv X x ≫ f := by
  apply InducedCategory.hom_ext
  exact derivedUnitH0NaturalLinearEquiv_naturality R f.hom x

/-- The actual H⁰ ring retains its preexisting additive group. -/
@[instance_reducible] def derivedH0CommRing (A : CommMon D) :
    CommRing ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  letI := commMonUnitHomCommRing D A
  exact addEquivCommRingPreservingAdd (boundedAboveUnitH0LinearEquiv A.X).toAddEquiv

/-- The cohomology-to-section comparison is a ring isomorphism for the actual H⁰ ring. -/
def derivedH0UnitHomRingEquiv (A : CommMon D) :
    letI := derivedH0CommRing A
    letI := commMonUnitHomCommRing D A
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ≃+* (𝟙_ D ⟶ A.X) := by
  letI := derivedH0CommRing A
  letI := commMonUnitHomCommRing D A
  exact
    { (boundedAboveUnitH0LinearEquiv A.X).toAddEquiv with
      map_mul' := fun x y ↦ (boundedAboveUnitH0LinearEquiv A.X).apply_symm_apply _ }

/-- The actual H⁰ product is the original derived product under unit representability. -/
theorem derivedH0_mul_normalization (A : CommMon D)
    (x y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    letI := derivedH0CommRing A
    boundedAboveUnitH0LinearEquiv A.X (x * y) =
      (λ_ (𝟙_ D)).inv ≫
        (boundedAboveUnitH0LinearEquiv A.X x ⊗ₘ boundedAboveUnitH0LinearEquiv A.X y) ≫
          A.mon.mul := by
  let := derivedH0CommRing A
  let := commMonUnitHomCommRing D A
  change (boundedAboveUnitH0LinearEquiv A.X)
    ((boundedAboveUnitH0LinearEquiv A.X).symm
      (boundedAboveUnitH0LinearEquiv A.X x * boundedAboveUnitH0LinearEquiv A.X y)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact commMonUnitHom_mul D A _ _

/-- The H⁰ unit is the image of the original derived algebra unit. -/
theorem derivedH0_one_normalization (A : CommMon D) :
    letI := derivedH0CommRing A
    boundedAboveUnitH0LinearEquiv A.X 1 = A.mon.one := by
  let := derivedH0CommRing A
  let := commMonUnitHomCommRing D A
  exact ((boundedAboveUnitH0LinearEquiv A.X).apply_symm_apply 1).trans
    (commMonUnitHom_one D A)

/-- A derived algebra map induces a ring homomorphism on actual H⁰. -/
def derivedH0Map {A B : CommMon D} (f : A ⟶ B) :
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj →+*
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj := by
  letI := derivedH0CommRing A
  letI := derivedH0CommRing B
  letI := commMonUnitHomCommRing D A
  letI := commMonUnitHomCommRing D B
  exact (derivedH0UnitHomRingEquiv B).symm.toRingHom.comp
    ((commMonUnitHomMap D f).comp (derivedH0UnitHomRingEquiv A).toRingHom)

/-- The constructed ring homomorphism is the original actual H⁰ map. -/
theorem derivedH0Map_apply {A B : CommMon D} (f : A ⟶ B)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0Map f x = (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x := by
  change (boundedAboveUnitH0LinearEquiv B.X).symm
    (boundedAboveUnitH0LinearEquiv A.X x ≫ f.hom.hom) = _
  apply (boundedAboveUnitH0LinearEquiv B.X).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (boundedAboveUnitH0LinearEquiv_naturality (X := A.X) (Y := B.X) f.hom.hom x).symm

/-- The actual H⁰ algebra structure retains the preexisting R-module action. -/
@[instance_reducible] def derivedH0Algebra (A : CommMon D) :
    letI := derivedH0CommRing A
    Algebra R ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  letI := derivedH0CommRing A
  letI := commMonUnitHomCommRing D A
  letI := commMonUnitHomAlgebra D R A
  let e := boundedAboveUnitH0LinearEquiv A.X
  have hm (x y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
      e (x * y) = e x * e y := (derivedH0UnitHomRingEquiv A).map_mul x y
  apply Algebra.ofModule
  · intro r x y
    apply e.injective
    rw [hm, e.map_smul, e.map_smul, hm]
    exact commMonUnitHom_smul_mul D R A r (e x) (e y)
  · intro r x y
    apply e.injective
    rw [hm, e.map_smul, e.map_smul, hm]
    exact commMonUnitHom_mul_smul D R A r (e x) (e y)

/-- The scalar map on actual H⁰ is normalized by the original derived algebra unit. -/
theorem derivedH0_algebraMap_normalization (A : CommMon D) (r : R) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    boundedAboveUnitH0LinearEquiv A.X (algebraMap R _ r) = r • A.mon.one := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  change boundedAboveUnitH0LinearEquiv A.X (r • (1 :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)) = _
  rw [LinearEquiv.map_smul, derivedH0_one_normalization]

/-- Actual derived algebra maps induce R-algebra maps on actual H⁰. -/
def derivedH0AlgMap {A B : CommMon D} (f : A ⟶ B) :
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj →ₐ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj := by
  letI := derivedH0CommRing A
  letI := derivedH0CommRing B
  letI := derivedH0Algebra A
  letI := derivedH0Algebra B
  letI := A.mon
  letI := B.mon
  exact
    { derivedH0Map f with
      commutes' r := by
        apply (boundedAboveUnitH0LinearEquiv B.X).injective
        change boundedAboveUnitH0LinearEquiv B.X (derivedH0Map f (algebraMap R _ r)) = _
        rw [derivedH0Map_apply]
        calc
          _ = boundedAboveUnitH0LinearEquiv A.X (algebraMap R _ r) ≫ f.hom.hom :=
            boundedAboveUnitH0LinearEquiv_naturality f.hom.hom _
          _ = r • B.mon.one := by
            rw [derivedH0_algebraMap_normalization]
            simp only [Linear.smul_comp, IsMonHom.one_hom]
          _ = _ := (derivedH0_algebraMap_normalization B r).symm }

/-- Its underlying function remains the exact original H⁰ map. -/
theorem derivedH0AlgMap_apply {A B : CommMon D} (f : A ⟶ B)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap f x = (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x :=
  derivedH0Map_apply f x

/-- The actual H⁰ algebra map preserves identities. -/
theorem derivedH0AlgMap_id (A : CommMon D) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    derivedH0AlgMap (𝟙 A) = AlgHom.id R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  apply AlgHom.ext
  intro x
  rw [derivedH0AlgMap_apply]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map (𝟙 A.X.obj) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The actual H⁰ algebra map preserves composition. -/
theorem derivedH0AlgMap_comp {A B C : CommMon D} (f : A ⟶ B) (g : B ⟶ C) :
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0CommRing C
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    letI := derivedH0Algebra C
    derivedH0AlgMap (f ≫ g) = (derivedH0AlgMap g).comp (derivedH0AlgMap f) := by
  let := derivedH0CommRing A
  let := derivedH0CommRing B
  let := derivedH0CommRing C
  let := derivedH0Algebra A
  let := derivedH0Algebra B
  let := derivedH0Algebra C
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply, derivedH0AlgMap_apply]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (f.hom.hom.hom ≫ g.hom.hom.hom) x = _
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- The transferred ring has exactly the original additive group on actual H⁰. -/
theorem derivedH0CommRing_addCommGroup (A : CommMon D) :
    (derivedH0CommRing A).toAddCommGroup =
      (inferInstance : AddCommGroup
        ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)) := rfl

/-- The algebra's induced module is exactly the original module on actual H⁰. -/
theorem derivedH0Algebra_module (A : CommMon D) :
    letI := derivedH0CommRing A
    let M := (inferInstance : Module R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj))
    letI := derivedH0Algebra A
    (Algebra.toModule : Module R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)) = M := by
  rfl

end SerrePositivity
