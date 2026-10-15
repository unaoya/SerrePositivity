module
public import SerrePositivity.HomologicalAlgebra.DerivedAlgebraObjects

/-! # Standard algebra morphisms and factors of the actual derived tensor algebra -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- An ordinary algebra morphism induces the existing degree-zero derived map
as a morphism of actual commutative algebra objects. -/
def boundedAboveDerivedAlgebraMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : boundedAboveDerivedAlgebra (R := R) A ⟶
      boundedAboveDerivedAlgebra (R := R) B := by
  letI := boundedAboveDerivedAlgebraMonObj (R := R) A
  letI := boundedAboveDerivedAlgebraMonObj (R := R) B
  let g := boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap)
  letI : IsMonHom g :=
    { one_hom := boundedAboveDerivedAlgebraUnit_naturality f
      mul_hom := (boundedAboveDerivedAlgebraMul_naturality f).symm }
  exact CommMon.homMk (Mon.Hom.mk g)

/-- The left factor enters the actual derived tensor by the standard right unitor and unit. -/
def boundedAboveDerivedTensorAlgebraLeft
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedAlgebra (R := R) S ⟶ boundedAboveDerivedTensorAlgebra (R := R) S T := by
  let B := boundedAboveDerivedAlgebra (R := R) S
  let C := boundedAboveDerivedAlgebra (R := R) T
  let e : Mon.trivial (DerivedCategory.Minus (ModuleCat.{u} R)) ⟶ C.toMon := default
  let f : B.toMon ⟶ B.toMon ⊗ C.toMon := (ρ_ B.toMon).inv ≫ B.toMon ◁ e
  exact CommMon.homMk f

/-- The right factor enters the actual derived tensor by the standard left unitor and unit. -/
def boundedAboveDerivedTensorAlgebraRight
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedAlgebra (R := R) T ⟶ boundedAboveDerivedTensorAlgebra (R := R) S T := by
  let B := boundedAboveDerivedAlgebra (R := R) S
  let C := boundedAboveDerivedAlgebra (R := R) T
  let e : Mon.trivial (DerivedCategory.Minus (ModuleCat.{u} R)) ⟶ B.toMon := default
  let f : C.toMon ⟶ B.toMon ⊗ C.toMon := (λ_ C.toMon).inv ≫ e ▷ C.toMon
  exact CommMon.homMk f

/-- The algebra map has precisely the established degree-zero underlying derived map. -/
@[simp] lemma boundedAboveDerivedAlgebraMap_hom
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    (boundedAboveDerivedAlgebraMap f).hom.hom =
      boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap) := rfl

/-- The left factor map uses exactly the actual right unitor and the right algebra unit. -/
lemma boundedAboveDerivedTensorAlgebraLeft_hom
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (boundedAboveDerivedTensorAlgebraLeft (R := R) S T).hom.hom =
      (boundedAboveDerivedTensorRightUnitor
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).inv ≫
      boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)))
        (boundedAboveDerivedAlgebraUnit (R := R) T)) := rfl

/-- The right factor map uses exactly the actual left unitor and the left algebra unit. -/
lemma boundedAboveDerivedTensorAlgebraRight_hom
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (boundedAboveDerivedTensorAlgebraRight (R := R) S T).hom.hom =
      (boundedAboveDerivedTensorLeftUnitor
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))).inv ≫
      boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedAlgebraUnit (R := R) S)
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))) := rfl

end SerrePositivity
