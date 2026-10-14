module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveProjectiveResolution

/-! # Functoriality of bounded-above projective replacements in the homotopy category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity
variable {C : Type u} [Category.{v} C] [Abelian C]
attribute [local instance] HasDerivedCategory.standard

/-- Maps out of a K-projective complex that agree in the derived category are homotopic. -/
def homotopyOfDerivedMapEq {P X : CochainComplex C ℤ} [P.IsKProjective]
    (f g : P ⟶ X) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKProjective.Qh_map_bijective P _).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app X)).mp
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, h]

namespace BoundedAboveProjectiveResolution
variable {K L M : CochainComplex C ℤ}

/-- Lift a map between the original complexes to their replacements. -/
def map (P : BoundedAboveProjectiveResolution K) (Q : BoundedAboveProjectiveResolution L)
    (f : K ⟶ L) : P.complex ⟶ Q.complex :=
  (exists_lift_of_quasiIso Q.π (P.π ≫ f)).choose

def mapHomotopy (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f : K ⟶ L) :
    Homotopy (map P Q f ≫ Q.π) (P.π ≫ f) :=
  (exists_lift_of_quasiIso Q.π (P.π ≫ f)).choose_spec.some

lemma map_naturality (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f : K ⟶ L) :
    DerivedCategory.Q.map (map P Q f) ≫ DerivedCategory.Q.map Q.π =
      DerivedCategory.Q.map P.π ≫ DerivedCategory.Q.map f := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy C (mapHomotopy P Q f)

/-- Lifts are unique up to homotopy; this also controls all choices in composition. -/
def homotopyOfAugmentation (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f g : P.complex ⟶ Q.complex)
    (h : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map Q.π =
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map Q.π) : Homotopy f g :=
  homotopyOfDerivedMapEq f g ((cancel_mono (DerivedCategory.Q.map Q.π)).mp h)

def mapIdHomotopy (P : BoundedAboveProjectiveResolution K) :
    Homotopy (map P P (𝟙 K)) (𝟙 P.complex) := by
  apply homotopyOfAugmentation P P
  rw [map_naturality]
  simp

def mapCompHomotopy (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (T : BoundedAboveProjectiveResolution M)
    (f : K ⟶ L) (g : L ⟶ M) :
    Homotopy (map P T (f ≫ g)) (map P Q f ≫ map Q T g) := by
  apply homotopyOfAugmentation P T
  rw [map_naturality, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [map_naturality Q T g,
    ← Category.assoc (DerivedCategory.Q.map (map P Q f)), map_naturality P Q f,
    Category.assoc]

lemma map_quasiIso (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (map P Q f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : IsIso (DerivedCategory.Q.map (map P Q f) ≫ DerivedCategory.Q.map Q.π) := by
    rw [map_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map Q.π)
end BoundedAboveProjectiveResolution

/-- Strictly bounded-above cochain complexes, with arbitrary chain maps. -/
abbrev BoundedAboveCochain (C : Type u) [Category.{v} C] [Abelian C] :=
  (show ObjectProperty (CochainComplex C ℤ) from fun K => ∃ n : ℤ, K.IsStrictlyLE n).FullSubcategory

/-- Choose a replacement for every object of the bounded-above category. -/
def boundedAboveChosenResolution [EnoughProjectives C] (K : BoundedAboveCochain C) :
    BoundedAboveProjectiveResolution K.obj := by
  have := K.property.choose_spec
  exact BoundedAboveProjectiveResolution.ofBoundedAbove K.obj K.property.choose

/-- Projective replacement is a functor after passing to homotopy classes. -/
def boundedAboveResolutionFunctor [EnoughProjectives C] :
    BoundedAboveCochain C ⥤ HomotopyCategory C (.up ℤ) where
  obj K := (HomotopyCategory.quotient C (.up ℤ)).obj (boundedAboveChosenResolution K).complex
  map {K L} f := (HomotopyCategory.quotient C (.up ℤ)).map
    (BoundedAboveProjectiveResolution.map (boundedAboveChosenResolution K)
      (boundedAboveChosenResolution L) f.hom)
  map_id K := by
    rw [← CategoryTheory.Functor.map_id]
    exact HomotopyCategory.eq_of_homotopy _ _
      (BoundedAboveProjectiveResolution.mapIdHomotopy (boundedAboveChosenResolution K))
  map_comp {K L M} f g := by
    rw [← CategoryTheory.Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _
      (BoundedAboveProjectiveResolution.mapCompHomotopy (boundedAboveChosenResolution K)
        (boundedAboveChosenResolution L) (boundedAboveChosenResolution M) f.hom g.hom)

end SerrePositivity
