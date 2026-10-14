module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedCone
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Distinguished cone triangles for the actual bounded-above left derived functor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- The standard cone projection, using the actual shift inside the bounded-above category. -/
def boundedAboveDerivedConeProjection {X : DerivedCategory.Minus C} {Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y)
    (f : P.complex ⟶ Q.complex) : boundedAboveDerivedConeObject P Q f ⟶ X⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
    (P.shiftMinus 1).iso.hom)

/-- Computing the third cone morphism preserves the mapped cone projection and its shift. -/
lemma boundedAboveLeftDerivedConeIso_projection_model [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] {X : DerivedCategory.Minus C} {Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y)
    (f : P.complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q f)).hom ≫
        (boundedAboveLeftDerivedModelIso F (X⟦(1 : ℤ)⟧) (P.shiftMinus 1)).hom ≫
        DerivedCategory.Q.map
          (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app P.complex).hom ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) =
      (boundedAboveLeftDerivedConeIso F P Q f).hom ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) := by
  have hn := boundedAboveLeftDerivedModelIso_naturality F (P.cone Q f) (P.shiftMinus 1)
    (boundedAboveDerivedConeProjection P Q f) (CochainComplex.mappingCone.triangle f).mor₃
    (by simp [BoundedAboveDerivedModel.cone, boundedAboveDerivedConeProjection])
  have hδ : (F.mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app P.complex).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso f F).hom ≫
        (CochainComplex.mappingCone.triangle ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ :=
    CochainComplex.mappingCone.map_δ f F
  simp only [boundedAboveLeftDerivedConeIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hδ,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- The chosen-model cone projection is compatible with the canonical derived shift comparison. -/
lemma boundedAboveLeftDerivedConeIso_projection [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] (X : DerivedCategory.Minus C) {Y : DerivedCategory C}
    (Q : BoundedAboveDerivedModel Y) (f : (boundedAboveDerivedChosenModel X).complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).map
        (boundedAboveDerivedConeProjection (boundedAboveDerivedChosenModel X) Q f)).hom ≫
        (boundedAboveLeftDerivedShiftIso F X 1).hom ≫
        (boundedAboveLeftDerivedModelIso F X (boundedAboveDerivedChosenModel X)).hom⟦(1 : ℤ)⟧' =
      (boundedAboveLeftDerivedConeIso F (boundedAboveDerivedChosenModel X) Q f).hom ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj (boundedAboveDerivedChosenModel X).complex) := by
  simp only [boundedAboveLeftDerivedShiftIso, id_eq, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact boundedAboveLeftDerivedConeIso_projection_model F (boundedAboveDerivedChosenModel X) Q f

/-- The actual left-derived images of a morphism, its cone inclusion and its cone projection. -/
def boundedAboveLeftDerivedConeTriangle [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) : Triangle (DerivedCategory E) :=
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  Triangle.mk ((boundedAboveLeftDerived F).map f).hom
    ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeInr P Q h)).hom
    (((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q h)).hom ≫
      (boundedAboveLeftDerivedShiftIso F X 1).hom)

/-- Compare the actual derived image triangle with the canonical mapped-complex cone triangle. -/
def boundedAboveLeftDerivedConeTriangleIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    boundedAboveLeftDerivedConeTriangle F f ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        ((F.mapHomologicalComplex (.up ℤ)).map
          ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom))) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  refine Triangle.isoMk _ _ (boundedAboveLeftDerivedModelIso F X P)
    (boundedAboveLeftDerivedModelIso F Y Q) (boundedAboveLeftDerivedConeIso F P Q h) ?_ ?_ ?_
  · exact boundedAboveLeftDerivedModelIso_naturality F P Q f h (P.map_naturality Q f.hom)
  · exact boundedAboveLeftDerivedConeIso_inr F P Q h
  · change (((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q h)).hom ≫
      (boundedAboveLeftDerivedShiftIso F X 1).hom) ≫
        (boundedAboveLeftDerivedModelIso F X P).hom⟦(1 : ℤ)⟧' =
      (boundedAboveLeftDerivedConeIso F P Q h).hom ≫
        (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (.up ℤ)).map h)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P.complex))
    simpa only [Category.assoc] using boundedAboveLeftDerivedConeIso_projection F X Q h

/-- The actual left-derived image triangles are distinguished for any additive F. -/
lemma boundedAboveLeftDerivedConeTriangle_distinguished [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    boundedAboveLeftDerivedConeTriangle F f ∈ distTriang (DerivedCategory E) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
    (boundedAboveLeftDerivedConeTriangleIso F f)

/-- Homology is exact on the actual left-derived cone triangle in every degree. -/
lemma boundedAboveLeftDerivedConeTriangle_homology_exact [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) (i : ℤ) :
    ((shortComplexOfDistTriangle (boundedAboveLeftDerivedConeTriangle F f)
      (boundedAboveLeftDerivedConeTriangle_distinguished F f)).map
        (DerivedCategory.homologyFunctor E i)).Exact :=
  (DerivedCategory.homologyFunctor E i).map_distinguished_exact _
    (boundedAboveLeftDerivedConeTriangle_distinguished F f)

end SerrePositivity
