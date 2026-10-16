module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects

/-! # Algebra equivalences on the actual derived tensor factors -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- An algebra equivalence gives an isomorphism of the original single algebra objects. -/
def boundedAboveDerivedAlgebraIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) : boundedAboveDerivedAlgebra (R := R) A ≅
      boundedAboveDerivedAlgebra (R := R) B := by
  let f := boundedAboveDerivedAlgebraMap e.toAlgHom
  let i := boundedAboveDerivedSingleFunctor.mapIso e.toLinearEquiv.toModuleIso
  exact CommMon.mkIso i f.hom.isMonHom_hom.one_hom f.hom.isMonHom_hom.mul_hom

/-- Tensoring the two original algebra isomorphisms preserves the actual algebra product. -/
def boundedAboveDerivedTensorAlgebraIso
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    boundedAboveDerivedTensorAlgebra (R := R) S T ≅
      boundedAboveDerivedTensorAlgebra (R := R) S' T' := by
  let A := boundedAboveDerivedAlgebra (R := R) S
  let B := boundedAboveDerivedAlgebra (R := R) T
  let A' := boundedAboveDerivedAlgebra (R := R) S'
  let B' := boundedAboveDerivedAlgebra (R := R) T'
  let f := boundedAboveDerivedAlgebraMap eS.toAlgHom
  let g := boundedAboveDerivedAlgebraMap eT.toAlgHom
  let h : A.toMon ⊗ B.toMon ⟶ A'.toMon ⊗ B'.toMon := f.hom ⊗ₘ g.hom
  let i := MonoidalCategory.tensorIso
    (boundedAboveDerivedSingleFunctor.mapIso eS.toLinearEquiv.toModuleIso)
    (boundedAboveDerivedSingleFunctor.mapIso eT.toLinearEquiv.toModuleIso)
  exact CommMon.mkIso i h.isMonHom_hom.one_hom h.isMonHom_hom.mul_hom

/-- The forward tensor isomorphism uses the original single maps on both factors. -/
lemma boundedAboveDerivedTensorAlgebraIso_hom
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    (boundedAboveDerivedTensorAlgebraIso eS eT).hom.hom.hom =
      boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom eS.toLinearMap))
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom eT.toLinearMap))) := rfl

/-- The left factor is preserved with its original algebra unit. -/
lemma boundedAboveDerivedTensorAlgebraIso_left
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫
        (boundedAboveDerivedTensorAlgebraIso eS eT).hom =
      boundedAboveDerivedAlgebraMap eS.toAlgHom ≫
        boundedAboveDerivedTensorAlgebraLeft (R := R) S' T' := by
  let A := boundedAboveDerivedAlgebra (R := R) S
  let B := boundedAboveDerivedAlgebra (R := R) T
  let A' := boundedAboveDerivedAlgebra (R := R) S'
  let B' := boundedAboveDerivedAlgebra (R := R) T'
  let f := boundedAboveDerivedAlgebraMap eS.toAlgHom
  let g := boundedAboveDerivedAlgebraMap eT.toAlgHom
  letI : IsMonHom g.hom.hom := g.hom.isMonHom_hom
  apply CommMon.hom_ext
  change ((ρ_ A.X).inv ≫ (A.X ◁ B.mon.one)) ≫
    (f.hom.hom ⊗ₘ g.hom.hom) = f.hom.hom ≫ (ρ_ A'.X).inv ≫ (A'.X ◁ B'.mon.one)
  simp only [Category.assoc, whiskerLeft_comp_tensorHom, IsMonHom.one_hom,
    rightUnitor_inv_comp_tensorHom]
  rfl

/-- The right factor is preserved with its original algebra unit as well. -/
lemma boundedAboveDerivedTensorAlgebraIso_right
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫
        (boundedAboveDerivedTensorAlgebraIso eS eT).hom =
      boundedAboveDerivedAlgebraMap eT.toAlgHom ≫
        boundedAboveDerivedTensorAlgebraRight (R := R) S' T' := by
  let A := boundedAboveDerivedAlgebra (R := R) S
  let B := boundedAboveDerivedAlgebra (R := R) T
  let A' := boundedAboveDerivedAlgebra (R := R) S'
  let B' := boundedAboveDerivedAlgebra (R := R) T'
  let f := boundedAboveDerivedAlgebraMap eS.toAlgHom
  let g := boundedAboveDerivedAlgebraMap eT.toAlgHom
  letI : IsMonHom f.hom.hom := f.hom.isMonHom_hom
  apply CommMon.hom_ext
  change ((λ_ B.X).inv ≫ (A.mon.one ▷ B.X)) ≫
    (f.hom.hom ⊗ₘ g.hom.hom) = g.hom.hom ≫ (λ_ B'.X).inv ≫ (A'.mon.one ▷ B'.X)
  simp only [Category.assoc, whiskerRight_comp_tensorHom, IsMonHom.one_hom,
    leftUnitor_inv_comp_tensorHom]
  rfl

/-- Apply the actual algebra completion functor to the original tensor-factor isomorphism. -/
def boundedAboveCompletedTensorAlgebraIso (a : R)
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    DerivedCompletion.boundedAboveCompletedTensorAlgebra R a S T ≅
      DerivedCompletion.boundedAboveCompletedTensorAlgebra R a S' T' :=
  (DerivedCompletion.boundedAboveCompletionCommMonFunctor R a).mapIso
    (boundedAboveDerivedTensorAlgebraIso eS eT)

/-- The original completion units commute with the factor comparison as algebra morphisms. -/
lemma boundedAboveCompletedTensorAlgebraIso_unit (a : R)
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    DerivedCompletion.boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedTensorAlgebra (R := R) S T) ≫
        (boundedAboveCompletedTensorAlgebraIso a eS eT).hom =
      (boundedAboveDerivedTensorAlgebraIso eS eT).hom ≫
        DerivedCompletion.boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedTensorAlgebra (R := R) S' T') :=
  (DerivedCompletion.boundedAboveCompletionAlgebraUnit_naturality R a
    (boundedAboveDerivedTensorAlgebraIso eS eT).hom).symm

/-- The left factor diagram persists after actual completion. -/
lemma boundedAboveCompletedTensorAlgebraIso_left (a : R)
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    DerivedCompletion.boundedAboveCompletedTensorAlgebraLeft R a S T ≫
        (boundedAboveCompletedTensorAlgebraIso a eS eT).hom =
      boundedAboveDerivedAlgebraMap eS.toAlgHom ≫
        DerivedCompletion.boundedAboveCompletedTensorAlgebraLeft R a S' T' := by
  rw [DerivedCompletion.boundedAboveCompletedTensorAlgebraLeft, Category.assoc,
    boundedAboveCompletedTensorAlgebraIso_unit, ← Category.assoc,
    boundedAboveDerivedTensorAlgebraIso_left]
  rw [Category.assoc]
  rfl

/-- The right factor diagram persists after actual completion. -/
lemma boundedAboveCompletedTensorAlgebraIso_right (a : R)
    {S T S' T' : Type u} [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    (eS : S ≃ₐ[R] S') (eT : T ≃ₐ[R] T') :
    DerivedCompletion.boundedAboveCompletedTensorAlgebraRight R a S T ≫
        (boundedAboveCompletedTensorAlgebraIso a eS eT).hom =
      boundedAboveDerivedAlgebraMap eT.toAlgHom ≫
        DerivedCompletion.boundedAboveCompletedTensorAlgebraRight R a S' T' := by
  rw [DerivedCompletion.boundedAboveCompletedTensorAlgebraRight, Category.assoc,
    boundedAboveCompletedTensorAlgebraIso_unit, ← Category.assoc,
    boundedAboveDerivedTensorAlgebraIso_right]
  rw [Category.assoc]
  rfl

end SerrePositivity
