module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveResolutionFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Projective representatives of bounded-above derived objects -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every derived morphism out of a K-projective complex has a chain representative. -/
lemma exists_cochainMap_of_isKProjective {P X : CochainComplex C ℤ} [P.IsKProjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj X) :
    ∃ g : P ⟶ X, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P _).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ f ≫
      (DerivedCategory.quotientCompQhIso C).inv.app X)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- A bounded-above projective representative with an isomorphism to the actual derived object. -/
structure BoundedAboveDerivedModel (X : DerivedCategory C) where
  complex : CochainComplex C ℤ
  bound : ℤ
  bounded : complex.IsStrictlyLE bound
  projective : ∀ i, Projective (complex.X i)
  iso : DerivedCategory.Q.obj complex ≅ X

namespace BoundedAboveDerivedModel
attribute [instance] bounded projective
variable {X Y Z : DerivedCategory C}
instance isKProjective (P : BoundedAboveDerivedModel X) : P.complex.IsKProjective :=
  CochainComplex.isKProjective_of_projective P.complex P.bound

/-- A representative exists for every bounded-above derived object. -/
def ofIsLE [EnoughProjectives C] (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    BoundedAboveDerivedModel X := Classical.choice (by
  obtain ⟨K, hb, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X n
  let P := BoundedAboveProjectiveResolution.ofBoundedAbove K n
  exact ⟨⟨P.complex, P.bound, inferInstance, inferInstance,
    asIso (DerivedCategory.Q.map P.π) ≪≫ e.symm⟩⟩)

/-- A chain representative of a derived morphism, using the specified model isomorphisms. -/
def map (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : X ⟶ Y) :
    P.complex ⟶ Q.complex :=
  (exists_cochainMap_of_isKProjective (P.iso.hom ≫ f ≫ Q.iso.inv)).choose

lemma map_Q (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : X ⟶ Y) :
    DerivedCategory.Q.map (map P Q f) = P.iso.hom ≫ f ≫ Q.iso.inv :=
  (exists_cochainMap_of_isKProjective (P.iso.hom ≫ f ≫ Q.iso.inv)).choose_spec

lemma map_naturality (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) :
    DerivedCategory.Q.map (map P Q f) ≫ Q.iso.hom = P.iso.hom ≫ f := by
  rw [map_Q]
  simp

def mapIdHomotopy (P : BoundedAboveDerivedModel X) :
    Homotopy (map P P (𝟙 X)) (𝟙 P.complex) :=
  homotopyOfDerivedMapEq _ _ (by rw [map_Q]; simp)

def mapCompHomotopy (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (T : BoundedAboveDerivedModel Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (map P T (f ≫ g)) (map P Q f ≫ map Q T g) :=
  homotopyOfDerivedMapEq _ _ (by rw [Functor.map_comp, map_Q, map_Q, map_Q]; simp)

lemma map_quasiIso (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) [IsIso f] : QuasiIso (map P Q f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, map_Q]
  infer_instance

/-- Comparing models is compatible with every derived morphism, up to homotopy. -/
def mapSquareHomotopy (P P' : BoundedAboveDerivedModel X)
    (Q Q' : BoundedAboveDerivedModel Y) (f : X ⟶ Y) :
    Homotopy (map P Q f ≫ map Q Q' (𝟙 Y)) (map P P' (𝟙 X) ≫ map P' Q' f) :=
  homotopyOfDerivedMapEq _ _ (by rw [Functor.map_comp, Functor.map_comp,
    map_Q, map_Q, map_Q, map_Q]; simp)

/-- An augmented resolution is a model of the actual derived image of its original complex. -/
def ofResolution {K : CochainComplex C ℤ} (P : BoundedAboveProjectiveResolution K) :
    BoundedAboveDerivedModel (DerivedCategory.Q.obj K) where
  complex := P.complex
  bound := P.bound
  bounded := inferInstance
  projective := inferInstance
  iso := asIso (DerivedCategory.Q.map P.π)

/-- The model lift of a localized chain map agrees with the augmented resolution lift. -/
def ofResolutionMapHomotopy {K L : CochainComplex C ℤ}
    (P : BoundedAboveProjectiveResolution K) (Q : BoundedAboveProjectiveResolution L)
    (f : K ⟶ L) :
    Homotopy (map (ofResolution P) (ofResolution Q) (DerivedCategory.Q.map f)) (P.map Q f) := by
  apply homotopyOfDerivedMapEq
  apply (cancel_mono (DerivedCategory.Q.map Q.π)).mp
  exact (map_naturality (ofResolution P) (ofResolution Q) (DerivedCategory.Q.map f)).trans
    (P.map_naturality Q f).symm

/-- Any chain map inducing the specified derived morphism agrees with its chosen lift. -/
def mapHomotopyOfNaturality (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f) :
    Homotopy (map P Q f) h := by
  apply homotopyOfDerivedMapEq
  apply (cancel_mono Q.iso.hom).mp
  exact (map_naturality P Q f).trans hh.symm

end BoundedAboveDerivedModel

/-- Choose a projective model for each object of Mathlib's actual bounded-above derived category. -/
def boundedAboveDerivedChosenModel [EnoughProjectives C] (X : DerivedCategory.Minus C) :
    BoundedAboveDerivedModel X.obj := by
  have := X.property.choose_spec
  exact BoundedAboveDerivedModel.ofIsLE X.obj X.property.choose

/-- Restrict the standard derived localization to the bounded-above objects. -/
def boundedAboveDerivedQ : BoundedAboveCochain C ⥤ DerivedCategory.Minus C where
  obj K := by
    have := K.property.choose_spec
    exact ⟨DerivedCategory.Q.obj K.obj, ⟨K.property.choose, inferInstance⟩⟩
  map f := ObjectProperty.homMk (DerivedCategory.Q.map f.hom)
  map_id K := by
    apply InducedCategory.hom_ext
    change DerivedCategory.Q.map (𝟙 K.obj) = 𝟙 (DerivedCategory.Q.obj K.obj)
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    apply InducedCategory.hom_ext
    change DerivedCategory.Q.map (f.hom ≫ g.hom) = _
    exact CategoryTheory.Functor.map_comp _ _ _

end SerrePositivity
