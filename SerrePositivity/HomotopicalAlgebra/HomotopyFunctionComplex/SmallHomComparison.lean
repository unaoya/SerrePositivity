module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftWeakEquivalence

/-! # The small-Hom mapping bifunctor and its natural universe comparison

The equivalence changing the representation of Hom sets constructs an
actual bifunctor. Full faithfulness compares it with the original Hom,
naturally in the cosimplicial source, target and simplicial degree.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

abbrev changeHom : C ⥤ ShrinkHoms C := (SmallHomModel.equivalence.{w} C).inverse

abbrev bifunctor : (SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  ((Functor.whiskeringRight SimplexCategory C (ShrinkHoms C)).obj (changeHom (C := C))).op ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
      (Functor.whiskeringLeft C (ShrinkHoms C) SSet.{w}).obj (changeHom (C := C))

def liftedHomEquiv (X Y : C) :
    ULift.{v} ((changeHom (C := C)).obj X ⟶ (changeHom (C := C)).obj Y) ≃
      ULift.{w} (X ⟶ Y) where
  toFun h := ⟨(changeHom (C := C)).preimage h.down⟩
  invFun f := ⟨(changeHom (C := C)).map f.down⟩
  left_inv h := ULift.ext ((changeHom (C := C)).map_preimage h.down)
  right_inv f := ULift.ext ((changeHom (C := C)).preimage_map f.down)

/-- An actual isomorphism of bifunctors, including source naturality. -/
def bifunctorLiftIso :
    bifunctor ⋙ (Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj
        SSet.uliftFunctor.{v, w} ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
        (Functor.whiskeringRight C SSet.{v} SSet.{max v w}).obj SSet.uliftFunctor.{w, v} :=
  NatIso.ofComponents (fun A => NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun n => Equiv.toIso (liftedHomEquiv (A.unop.obj n.unop) Y)) (by
      intro n m f
      ext h
      change ULift.{v} ((changeHom (C := C)).obj (A.unop.obj n.unop) ⟶
        (changeHom (C := C)).obj Y) at h
      apply ULift.ext
      change (changeHom (C := C)).preimage ((changeHom (C := C)).map (A.unop.map f.unop) ≫ h.down) =
        A.unop.map f.unop ≫ (changeHom (C := C)).preimage h.down
      apply (changeHom (C := C)).map_injective
      rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage])) (by
    intro Y Z f
    ext n h
    change ULift.{v} ((changeHom (C := C)).obj (A.unop.obj n.unop) ⟶
      (changeHom (C := C)).obj Y) at h
    apply ULift.ext
    change (changeHom (C := C)).preimage (h.down ≫ (changeHom (C := C)).map f) =
      (changeHom (C := C)).preimage h.down ≫ f
    apply (changeHom (C := C)).map_injective
    rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage])) (by
  intro A B a
  ext Y n h
  change ULift.{v} ((changeHom (C := C)).obj (A.unop.obj n.unop) ⟶
    (changeHom (C := C)).obj Y) at h
  apply ULift.ext
  change (changeHom (C := C)).preimage ((changeHom (C := C)).map (a.unop.app n.unop) ≫ h.down) =
    a.unop.app n.unop ≫ (changeHom (C := C)).preimage h.down
  apply (changeHom (C := C)).map_injective
  rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage])

abbrev hom (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C) : Cᵒᵖ ⥤ C ⥤ SSet.{w} :=
  Q.op ⋙ bifunctor ⋙ (Functor.whiskeringLeft C C SSet.{w}).obj R

def resolutionLiftIso (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C) :
    hom Q R ⋙ (Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj
        SSet.uliftFunctor.{v, w} ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R ⋙ (Functor.whiskeringRight C SSet.{v} SSet.{max v w}).obj
        SSet.uliftFunctor.{w, v} :=
  NatIso.ofComponents (fun X =>
    Functor.isoWhiskerLeft R (bifunctorLiftIso.app (Opposite.op (Q.obj X.unop)))) (by
      intro X Y f
      apply NatTrans.ext
      funext Z
      exact congr_app (bifunctorLiftIso.hom.naturality (Q.map f.unop).op) (R.obj Z))

def sourceArrowIso (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)
    {X Y : C} (f : X ⟶ Y) (Z : C) :
    Arrow.mk (SSet.uliftFunctor.{v, w}.map (((hom Q R).map f.op).app Z)) ≅
      Arrow.mk (SSet.uliftFunctor.{w, v}.map (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R).map f.op).app Z)) :=
  Arrow.isoMk (((resolutionLiftIso Q R).app (Opposite.op Y)).app Z)
    (((resolutionLiftIso Q R).app (Opposite.op X)).app Z)
    (congr_app ((resolutionLiftIso Q R).hom.naturality f.op) Z).symm

abbrev chosenHom
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :=
  hom (Reedy.cosimplicialResolutionFamily cof).obj (fibrantTarget fib)

end SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
