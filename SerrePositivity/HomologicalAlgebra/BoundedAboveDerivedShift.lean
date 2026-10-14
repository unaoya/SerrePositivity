module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveLeftDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Shifted projective representatives and left-derived shift comparisons -/
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

/-- Transport a projective representative along an actual derived isomorphism. -/
def BoundedAboveDerivedModel.transport {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (e : X ≅ Y) : BoundedAboveDerivedModel Y where
  complex := P.complex
  bound := P.bound
  bounded := P.bounded
  projective := P.projective
  iso := P.iso ≪≫ e

/-- Shift a bounded-above projective representative, retaining the actual derived shift. -/
def BoundedAboveDerivedModel.shift {X : DerivedCategory C} (P : BoundedAboveDerivedModel X)
    (n : ℤ) : BoundedAboveDerivedModel (X⟦n⟧) where
  complex := P.complex⟦n⟧
  bound := P.bound - n
  bounded := CochainComplex.isStrictlyLE_shift P.complex P.bound n (P.bound - n) (by omega)
  projective i := Projective.of_iso
    (CochainComplex.shiftFunctorObjXIso P.complex n i (i + n) rfl).symm inferInstance
  iso := (DerivedCategory.Q.commShiftIso n).app P.complex ≪≫
    (shiftFunctor (DerivedCategory C) n).mapIso P.iso

/-- A representative of a derived morphism shifts to a representative of its actual shift. -/
lemma BoundedAboveDerivedModel.shift_map_naturality {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f) (n : ℤ) :
    DerivedCategory.Q.map (h⟦n⟧') ≫ (Q.shift n).iso.hom =
      (P.shift n).iso.hom ≫ f⟦n⟧' := by
  have hn := (DerivedCategory.Q.commShiftIso n).hom.naturality h
  change DerivedCategory.Q.map (h⟦n⟧') ≫ (DerivedCategory.Q.commShiftIso n).hom.app Q.complex =
    (DerivedCategory.Q.commShiftIso n).hom.app P.complex ≫ (DerivedCategory.Q.map h)⟦n⟧' at hn
  simp only [BoundedAboveDerivedModel.shift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp, hh,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- Use the inclusion's shift isomorphism to model the actual full-subcategory shift. -/
def BoundedAboveDerivedModel.shiftMinus {X : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X.obj) (n : ℤ) : BoundedAboveDerivedModel (X⟦n⟧).obj :=
  (P.shift n).transport ((DerivedCategory.Minus.ι.commShiftIso n).app X).symm

/-- Shifted representatives respect the actual shift of a full-subcategory morphism. -/
lemma BoundedAboveDerivedModel.shiftMinus_map_naturality
    {X Y : DerivedCategory.Minus C} (P : BoundedAboveDerivedModel X.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f.hom) (n : ℤ) :
    DerivedCategory.Q.map (h⟦n⟧') ≫ (Q.shiftMinus n).iso.hom =
      (P.shiftMinus n).iso.hom ≫ (f⟦n⟧').hom := by
  simp only [BoundedAboveDerivedModel.shiftMinus, BoundedAboveDerivedModel.transport,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, P.shift_map_naturality Q f.hom h hh n, Category.assoc]
  congr 1
  exact (DerivedCategory.Minus.ι.commShiftIso n).inv.naturality f

/-- Compute the shift comparison of the left-derived functor using the chosen projective model. -/
def boundedAboveLeftDerivedShiftIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    (X : DerivedCategory.Minus C) (n : ℤ) :
    ((boundedAboveLeftDerived F).obj (X⟦n⟧)).obj ≅
      (((boundedAboveLeftDerived F).obj X).obj)⟦n⟧ := by
  let P := boundedAboveDerivedChosenModel X
  refine boundedAboveLeftDerivedModelIso F _ (P.shiftMinus n) ≪≫ ?_
  change DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj (P.complex⟦n⟧)) ≅ _
  exact DerivedCategory.Q.mapIso
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app P.complex) ≪≫
    (DerivedCategory.Q.commShiftIso n).app ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) ≪≫
    (shiftFunctor (DerivedCategory E) n).mapIso (boundedAboveLeftDerivedModelIso F X P).symm

/-- The left-derived shift comparison is natural in every actual derived morphism. -/
lemma boundedAboveLeftDerivedShiftIso_naturality [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) (n : ℤ) :
    ((boundedAboveLeftDerived F).map (f⟦n⟧')).hom ≫
        (boundedAboveLeftDerivedShiftIso F Y n).hom =
      (boundedAboveLeftDerivedShiftIso F X n).hom ≫
        (((boundedAboveLeftDerived F).map f).hom)⟦n⟧' := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  let Fh := (F.mapHomologicalComplex (.up ℤ)).map h
  have hm := boundedAboveLeftDerivedModelIso_naturality F (P.shiftMinus n) (Q.shiftMinus n)
    (f⟦n⟧') (h⟦n⟧') (P.shiftMinus_map_naturality Q f h (P.map_naturality Q f.hom) n)
  have hc := ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.naturality h
  change (F.mapHomologicalComplex (.up ℤ)).map (h⟦n⟧') ≫
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app Q.complex).hom =
    (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app P.complex).hom ≫ Fh⟦n⟧' at hc
  have hq := (DerivedCategory.Q.commShiftIso n).hom.naturality Fh
  change DerivedCategory.Q.map (Fh⟦n⟧') ≫
      ((DerivedCategory.Q.commShiftIso n).app
        ((F.mapHomologicalComplex (.up ℤ)).obj Q.complex)).hom =
    ((DerivedCategory.Q.commShiftIso n).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P.complex)).hom ≫
      (DerivedCategory.Q.map Fh)⟦n⟧' at hq
  have hb := boundedAboveLeftDerivedModelIso_naturality F P Q f h (P.map_naturality Q f.hom)
  have hi : DerivedCategory.Q.map Fh ≫ (boundedAboveLeftDerivedModelIso F Y Q).inv =
      (boundedAboveLeftDerivedModelIso F X P).inv ≫ ((boundedAboveLeftDerived F).map f).hom := by
    apply (cancel_epi (boundedAboveLeftDerivedModelIso F X P).hom).mp
    rw [← Category.assoc, ← hb]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simp only [boundedAboveLeftDerivedShiftIso, id_eq, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hm]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hc,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, hq, Category.assoc]
  congr 1
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg (shiftFunctor (DerivedCategory E) n).map hi

/-- A natural shift comparison on the standard bounded-above derived category. -/
def boundedAboveLeftDerivedShiftNatIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive] (n : ℤ) :
    shiftFunctor (DerivedCategory.Minus C) n ⋙ boundedAboveLeftDerived F ⋙ DerivedCategory.Minus.ι ≅
      (boundedAboveLeftDerived F ⋙ DerivedCategory.Minus.ι) ⋙ shiftFunctor (DerivedCategory E) n :=
  NatIso.ofComponents (fun X => boundedAboveLeftDerivedShiftIso F X n)
    (fun f => boundedAboveLeftDerivedShiftIso_naturality F f n)

end SerrePositivity
