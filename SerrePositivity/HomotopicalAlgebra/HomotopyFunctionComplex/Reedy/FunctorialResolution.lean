module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Resolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialFactorizationClasses

/-! # Functorial resolutions from chosen source factorization data

The constructed Reedy factorization functor is restricted to the arrows
from the initial diagram or to the terminal diagram of constant objects.
The comparison is a natural transformation in the original object of C.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
  {C : Type u'} [Category.{v'} C] [ModelCategory C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C]

abbrev initialConstantArrows : C ⥤ Arrow (J ⥤ C) where
  obj X := Arrow.mk (initial.to ((Functor.const J).obj X))
  map f := Arrow.homMk (𝟙 _) ((Functor.const J).map f) (by simp)

abbrev terminalConstantArrows : C ⥤ Arrow (J ⥤ C) where
  obj X := Arrow.mk (terminal.from ((Functor.const J).obj X))
  map f := Arrow.homMk ((Functor.const J).map f) (𝟙 _) (by simp)

structure CofibrantResolutionFamily where
  obj : C ⥤ (J ⥤ C)
  augmentation : obj ⟶ Functor.const J
  cofibrant : ∀ X, reedyLeft r (cofibrations C) (initial.to (obj.obj X))
  trivial : ∀ X, reedyRight r (trivialFibrations C) (augmentation.app X)

structure FibrantResolutionFamily where
  obj : C ⥤ (J ⥤ C)
  coaugmentation : Functor.const J ⟶ obj
  fibrant : ∀ X, reedyRight r (fibrations C) (terminal.from (obj.obj X))
  trivial : ∀ X, reedyLeft r (trivialCofibrations C) (coaugmentation.app X)

namespace CofibrantResolutionFamily
variable {r}

def atObject (q : CofibrantResolutionFamily (C := C) r) (X : C) : CofibrantResolution r X where
  obj := q.obj.obj X
  augmentation := q.augmentation.app X
  cofibrant := q.cofibrant X
  trivial := q.trivial X

lemma map_weakEquivalence (q : CofibrantResolutionFamily (C := C) r)
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) (j : J) :
    weakEquivalences C ((q.obj.map f).app j) := by
  have h := congr_app (q.augmentation.naturality f) j
  change (q.obj.map f).app j ≫ (q.augmentation.app Y).app j =
    (q.augmentation.app X).app j ≫ f at h
  have hc := (weakEquivalences C).comp_mem _ _
    ((q.atObject X).augmentation_weakEquivalence j) hf
  exact (weakEquivalences C).of_postcomp _ _
    ((q.atObject Y).augmentation_weakEquivalence j) (h.symm ▸ hc)

def ofFactorizationData (d : MorphismProperty.FunctorialFactorizationData
    (reedyLeft r (cofibrations C)) (reedyRight r (trivialFibrations C))) :
    CofibrantResolutionFamily (C := C) r where
  obj := initialConstantArrows (J := J) (C := C) ⋙ d.Z
  augmentation :=
    { app X := d.p.app ((initialConstantArrows (J := J) (C := C)).obj X)
      naturality {_ _} f := d.p.naturality ((initialConstantArrows (J := J) (C := C)).map f) }
  cofibrant X := by
    have he : d.i.app ((initialConstantArrows (J := J) (C := C)).obj X) =
        initial.to (d.Z.obj ((initialConstantArrows (J := J) (C := C)).obj X)) := by
      apply initial.hom_ext
    exact he ▸ d.hi _
  trivial X := d.hp _

end CofibrantResolutionFamily

namespace FibrantResolutionFamily
variable {r}

def atObject (q : FibrantResolutionFamily (C := C) r) (X : C) : FibrantResolution r X where
  obj := q.obj.obj X
  coaugmentation := q.coaugmentation.app X
  fibrant := q.fibrant X
  trivial := q.trivial X

lemma map_weakEquivalence (q : FibrantResolutionFamily (C := C) r)
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) (j : J) :
    weakEquivalences C ((q.obj.map f).app j) := by
  have h := congr_app (q.coaugmentation.naturality f) j
  change f ≫ (q.coaugmentation.app Y).app j =
    (q.coaugmentation.app X).app j ≫ (q.obj.map f).app j at h
  have hc := (weakEquivalences C).comp_mem _ _ hf
    ((q.atObject Y).coaugmentation_weakEquivalence j)
  exact (weakEquivalences C).of_precomp _ _
    ((q.atObject X).coaugmentation_weakEquivalence j) (h ▸ hc)

def ofFactorizationData (d : MorphismProperty.FunctorialFactorizationData
    (reedyLeft r (trivialCofibrations C)) (reedyRight r (fibrations C))) :
    FibrantResolutionFamily (C := C) r where
  obj := terminalConstantArrows (J := J) (C := C) ⋙ d.Z
  coaugmentation :=
    { app X := d.i.app ((terminalConstantArrows (J := J) (C := C)).obj X)
      naturality {_ _} f := d.i.naturality ((terminalConstantArrows (J := J) (C := C)).map f) }
  fibrant X := by
    have he : d.p.app ((terminalConstantArrows (J := J) (C := C)).obj X) =
        terminal.from (d.Z.obj ((terminalConstantArrows (J := J) (C := C)).obj X)) := by
      apply terminal.hom_ext
    exact he ▸ d.hp _
  trivial X := d.hi _

end FibrantResolutionFamily

def cofibrantResolutionFamily (hinj : Function.Injective r.deg)
    (hsurj : Function.Surjective r.deg)
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    CofibrantResolutionFamily (C := C) r :=
  CofibrantResolutionFamily.ofFactorizationData
    (FunctorFactorizationSequence.functorialFactorizationData r hinj hsurj source)

def fibrantResolutionFamily (hinj : Function.Injective r.deg)
    (hsurj : Function.Surjective r.deg)
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    FibrantResolutionFamily (C := C) r :=
  FibrantResolutionFamily.ofFactorizationData
    (FunctorFactorizationSequence.functorialFactorizationData r hinj hsurj source)

end SerrePositivity.Reedy
