module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModels

/-! # Left derived functors on the standard bounded-above derived category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]
variable (F : C ⥤ E) [F.Additive]

/-- An additive functor preserves quasi-isomorphisms between K-projective complexes. -/
lemma mapCochain_quasiIso_of_KProjective {P Q : CochainComplex C ℤ}
    [P.IsKProjective] [Q.IsKProjective] (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  have h : (F.mapHomotopyEquiv e).hom = (F.mapHomologicalComplex (.up ℤ)).map f := by
    simp [Functor.mapHomotopyEquiv, he]
  rw [← h]
  infer_instance

/-- Compute the left derived functor using bounded-above projective representatives.
The source and target are Mathlib's standard derived categories. -/
def boundedAboveLeftDerived [EnoughProjectives C] :
    DerivedCategory.Minus C ⥤ DerivedCategory.Minus E where
  obj X := by
    let P := boundedAboveDerivedChosenModel X
    exact ⟨DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P.complex),
      ⟨P.bound, inferInstance⟩⟩
  map {X Y} f := ObjectProperty.homMk (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map
      ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)))
  map_id X := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (P.map P (𝟙 X.obj))) = _
    rw [DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy P.mapIdHomotopy),
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    let Q := boundedAboveDerivedChosenModel Y
    let T := boundedAboveDerivedChosenModel Z
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (P.map T (f.hom ≫ g.hom))) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (P.map Q f.hom)) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (Q.map T g.hom))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy E
      (F.mapHomotopy (P.mapCompHomotopy Q T f.hom g.hom))

/-- Any bounded-above projective model computes the derived functor. -/
def boundedAboveLeftDerivedModelIso [EnoughProjectives C]
    (X : DerivedCategory.Minus C) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveLeftDerived F).obj X).obj ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) := by
  let A := boundedAboveDerivedChosenModel X
  have := A.map_quasiIso P (𝟙 X.obj)
  have := mapCochain_quasiIso_of_KProjective F (A.map P (𝟙 X.obj))
  exact asIso (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map (A.map P (𝟙 X.obj))))

/-- The computation with arbitrary models is natural in any representative of a derived morphism. -/
lemma boundedAboveLeftDerivedModelIso_naturality [EnoughProjectives C]
    {X Y : DerivedCategory.Minus C} (P : BoundedAboveDerivedModel X.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f.hom) :
    ((boundedAboveLeftDerived F).map f).hom ≫ (boundedAboveLeftDerivedModelIso F Y Q).hom =
      (boundedAboveLeftDerivedModelIso F X P).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map h) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel Y
  have ht := (A.mapSquareHomotopy P B Q f.hom).trans
    ((P.mapHomotopyOfNaturality Q f.hom h hh).compLeft (A.map P (𝟙 _)))
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (A.map B f.hom)) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (B.map Q (𝟙 _))) =
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (A.map P (𝟙 _))) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map h)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy ht)

end SerrePositivity
