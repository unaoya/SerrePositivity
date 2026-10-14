module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveLeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Additivity and linearity of the actual bounded-above left derived functor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe t v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- Chosen projective lifts respect addition up to homotopy. -/
def BoundedAboveDerivedModel.mapAddHomotopy {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f g : X ⟶ Y) :
    Homotopy (P.map Q (f + g)) (P.map Q f + P.map Q g) :=
  P.mapHomotopyOfNaturality Q (f + g) _ (by
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      P.map_naturality Q f, P.map_naturality Q g])

instance boundedAboveLeftDerived_additive (F : C ⥤ E) [F.Additive] :
    (boundedAboveLeftDerived F).Additive where
  map_add {X Y f g} := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    let Q := boundedAboveDerivedChosenModel Y
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (P.map Q (f.hom + g.hom))) = _
    rw [DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy
      (P.mapAddHomotopy Q f.hom g.hom)), Functor.map_add, Functor.map_add]
    rfl

variable (A : Type t) [CommRing A] [Linear A C] [Linear A E]

/-- Chosen projective lifts respect scalar multiplication up to homotopy. -/
def BoundedAboveDerivedModel.mapSmulHomotopy {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (a : A) (f : X ⟶ Y) :
    Homotopy (P.map Q (a • f)) (a • P.map Q f) :=
  P.mapHomotopyOfNaturality Q (a • f) _ (by
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, P.map_naturality Q f])

instance boundedAboveLeftDerived_linear (F : C ⥤ E) [F.Additive] [F.Linear A] :
    (boundedAboveLeftDerived F).Linear A where
  map_smul {X Y} f a := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    let Q := boundedAboveDerivedChosenModel Y
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (P.map Q (a • f.hom))) = _
    rw [DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy
      (P.mapSmulHomotopy A Q a f.hom)), Functor.map_smul, Functor.map_smul]
    rfl

end SerrePositivity
