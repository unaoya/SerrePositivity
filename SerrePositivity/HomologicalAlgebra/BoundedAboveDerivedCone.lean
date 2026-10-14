module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveLeftDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Projective cone models for bounded-above left derived functors

No exactness of the original additive functor is assumed. A cone of projective models
is again a projective model, so its derived image is computed by the actual mapped cone.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- The cone of bounded-above projective representatives is itself such a representative. -/
def BoundedAboveDerivedModel.cone {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : P.complex ⟶ Q.complex) :
    BoundedAboveDerivedModel (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) where
  complex := CochainComplex.mappingCone f
  bound := max P.bound Q.bound
  bounded := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P.complex.isZero_of_isStrictlyLE P.bound (i + 1) (by omega),
      Q.complex.isZero_of_isStrictlyLE Q.bound i (by omega)⟩
  projective i := Projective.of_iso
    (homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm inferInstance
  iso := Iso.refl _

/-- The actual bounded-above derived object of the model cone. -/
def boundedAboveDerivedConeObject {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : P.complex ⟶ Q.complex) :
    DerivedCategory.Minus C := by
  have : (CochainComplex.mappingCone f).IsStrictlyLE (max P.bound Q.bound) := (P.cone Q f).bounded
  exact ⟨DerivedCategory.Q.obj (CochainComplex.mappingCone f), ⟨max P.bound Q.bound, inferInstance⟩⟩

/-- The right cone inclusion, transported from any projective model of its actual source. -/
def boundedAboveDerivedConeInr {X : DerivedCategory C} {Y : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y.obj)
    (f : P.complex ⟶ Q.complex) : Y ⟶ boundedAboveDerivedConeObject P Q f :=
  ObjectProperty.homMk (Q.iso.inv ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr f))

/-- The derived image of a projective cone is computed by the actual mapped cone. -/
def boundedAboveLeftDerivedConeIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory C} (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : P.complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).obj (boundedAboveDerivedConeObject P Q f)).obj ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        ((F.mapHomologicalComplex (.up ℤ)).map f)) :=
  boundedAboveLeftDerivedModelIso F _ (P.cone Q f) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F)

/-- The derived cone computation preserves its standard right inclusion. -/
lemma boundedAboveLeftDerivedConeIso_inr [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X : DerivedCategory C} {Y : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y.obj)
    (f : P.complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeInr P Q f)).hom ≫
        (boundedAboveLeftDerivedConeIso F P Q f).hom =
      (boundedAboveLeftDerivedModelIso F Y Q).hom ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  have hn := boundedAboveLeftDerivedModelIso_naturality F Q (P.cone Q f)
    (boundedAboveDerivedConeInr P Q f) (CochainComplex.mappingCone.inr f) (by
      simp [BoundedAboveDerivedModel.cone, boundedAboveDerivedConeInr])
  simp only [boundedAboveLeftDerivedConeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, CochainComplex.mappingCone.map_inr]

end SerrePositivity
