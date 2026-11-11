module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-! # Comparing one weakly augmented frame with a specified resolution

The comparison maps are actual natural transformations in the target.
The augmentation of the frame is only a weak equivalence degreewise;
it need not be a trivial fibration.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.FrameOverObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex)
  (X : C) (A : SimplexCategory ⥤ C) (a : A ⟶ (Functor.const SimplexCategory).obj X)

abbrev parameter : Type := Discrete PUnit.{1}
abbrev point : parameter := ⟨PUnit.unit⟩
abbrev target : parameter ⥤ C := (Functor.const parameter).obj X
abbrev family : parameter ⥤ SimplexCategory ⥤ C := (Functor.const parameter).obj A

def familyAugmentation : family A ⟶ target X ⋙ Functor.const SimplexCategory where
  app _ := a
  naturality := by intros; simp

abbrev middle : C ⥤ SSet.{v} :=
  (FrameOverFunctor.hom (FrameOverFunctor.commonObj cof q (target X) (family A)
    (familyAugmentation X A a))).obj (Opposite.op point)

abbrev left : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (q.obj.obj X) ⟶ middle cof q X A a :=
  (FrameOverFunctor.homLeft cof q (target X) (family A)
    (familyAugmentation X A a)).app (Opposite.op point)

abbrev right : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A ⟶ middle cof q X A a :=
  (FrameOverFunctor.homRight cof q (target X) (family A)
    (familyAugmentation X A a)).app (Opposite.op point)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma left_weakEquivalence (ha : ∀ n, weakEquivalences C (a.app n))
    (Y : C) [IsFibrant Y] : weakEquivalences SSet.{v} ((left cof q X A a).app Y) :=
  FrameOverFunctor.homLeft_weakEquivalence cof q (target X) (family A)
    (familyAugmentation X A a) hcof (fun _ n => ha n) (Opposite.op point) Y

include hcof in
lemma right_weakEquivalence (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (Y : C) [IsFibrant Y] : weakEquivalences SSet.{v} ((right cof q X A a).app Y) :=
  FrameOverFunctor.homRight_weakEquivalence cof q (target X) (family A)
    (familyAugmentation X A a) hcof (fun _ => hA) (Opposite.op point) Y

end SerrePositivity.HomotopyFunctionComplex.FrameOverObject
