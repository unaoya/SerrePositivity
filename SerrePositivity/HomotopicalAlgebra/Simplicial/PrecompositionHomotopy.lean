module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CurriedHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-! # Actual interval homotopies act contravariantly on internal Hom

The interval is retained through an explicit reassociation of the three
factors. Postcomposition in the original homotopy becomes precomposition
in the mapping space, and constant intervals remain exactly constant.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.PrecompositionHomotopy

def shuffle (A Z : SSet.{v}) :
    A ⊗ (Z ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ⟶
      (A ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ⊗ Z where
  app _ := ↾fun x => ((x.1, x.2.2), x.2.1)
  naturality _ _ _ := by ext x; rfl

lemma shuffle_zero (A Z : SSet.{v}) :
    A ◁ (SSet.ι₀ (X := Z)) ≫ shuffle A Z = (SSet.ι₀ (X := A)) ▷ Z := by
  apply NatTrans.ext
  funext n
  exact ConcreteCategory.hom_ext _ _ (fun x => rfl)

lemma shuffle_one (A Z : SSet.{v}) :
    A ◁ (SSet.ι₁ (X := Z)) ≫ shuffle A Z = (SSet.ι₁ (X := A)) ▷ Z := by
  apply NatTrans.ext
  funext n
  exact ConcreteCategory.hom_ext _ _ (fun x => rfl)

lemma shuffle_natural {Z Z' : SSet.{v}} (A : SSet.{v}) (z : Z ⟶ Z') :
    A ◁ (z ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ shuffle A Z' =
      shuffle A Z ≫ (A ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ◁ z := by
  apply NatTrans.ext
  funext n
  exact ConcreteCategory.hom_ext _ _ (fun x => rfl)

lemma shuffle_fst (A Z : SSet.{v}) :
    shuffle A Z ≫ (fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1))) ▷ Z =
      A ◁ fst Z (SSet.stdSimplex.obj (SimplexCategory.mk 1)) := by
  apply NatTrans.ext
  funext n
  exact ConcreteCategory.hom_ext _ _ (fun x => rfl)

variable {A B C : SSet.{v}} {f g : A ⟶ B}

def interval (H : SSet.Homotopy f g) (K : SSet.{v}) :
    (ihom B).obj K ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ (ihom A).obj K :=
  curry (shuffle A ((ihom B).obj K) ≫ H.h ▷ (ihom B).obj K ≫ (ihom.ev B).app K)

def homotopy (H : SSet.Homotopy f g) (K : SSet.{v}) :
    SSet.Homotopy ((MonoidalClosed.pre f).app K) ((MonoidalClosed.pre g).app K) where
  h := interval H K
  h₀ := by
    change SSet.ι₀ ≫ interval H K = (MonoidalClosed.pre f).app K
    apply uncurry_injective
    rw [uncurry_natural_left]
    dsimp only [interval]
    rw [uncurry_curry, ← Category.assoc, shuffle_zero, ← Category.assoc,
      ← comp_whiskerRight, H.h₀, uncurry_pre]
  h₁ := by
    change SSet.ι₁ ≫ interval H K = (MonoidalClosed.pre g).app K
    apply uncurry_injective
    rw [uncurry_natural_left]
    dsimp only [interval]
    rw [uncurry_curry, ← Category.assoc, shuffle_one, ← Category.assoc,
      ← comp_whiskerRight, H.h₁, uncurry_pre]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

lemma interval_post (H : SSet.Homotopy f g) (p : B ⟶ C) (K : SSet.{v}) :
    ((MonoidalClosed.pre p).app K) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ interval H K =
      interval (HomotopyClasses.postHomotopy p H) K := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  dsimp only [interval]
  rw [uncurry_curry, uncurry_curry, ← Category.assoc, shuffle_natural, Category.assoc,
    whisker_exchange_assoc, id_tensor_pre_app_comp_ev]
  change _ = shuffle A ((ihom C).obj K) ≫ (H.h ≫ p) ▷ (ihom C).obj K ≫ _
  simp only [comp_whiskerRight, Category.assoc]

lemma interval_constant (H : SSet.Homotopy f g) (K : SSet.{v}) (e : A ⟶ B)
    (he : H.h = fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ e) :
    interval H K = fst ((ihom B).obj K) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      (MonoidalClosed.pre e).app K := by
  apply uncurry_injective
  dsimp only [interval]
  rw [uncurry_curry, he, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (shuffle A _) (fst A _ ▷ _) (e ▷ _ ≫ _), shuffle_fst,
    uncurry_natural_left, uncurry_pre]

end SerrePositivity.SimplicialModel.PrecompositionHomotopy
