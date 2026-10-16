module

public import SerrePositivity.CategoryTheory.Presentation.RetractWordAugmentation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationCat
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering

/-! # Natural augmentation of the simplicial word construction and its two-direction diagrams

The common category universe contains object, Hom, and word universes.
No model structure is used on any category of simplicial sets.
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.WordPresentationAugmentation
open WordPresentationCat

def augmentation (M : Type w) [MonoidWithZero M] :
    functor.{u, max u v w} M ⟶ 𝟭 Cat.{max u v w, u} where
  app C := (RetractWords.augmentation C M).toCatHom
  naturality {_ _} F := by
    apply Cat.Hom.ext
    exact RetractWords.map_augmentation F.toFunctor (MonoidWithZeroHom.id M)

lemma augmentation_change {M N : Type w} [MonoidWithZero M] [MonoidWithZero N]
    (h : M →*₀ N) : changeParameters.{u, max u v w} h ≫ augmentation.{u, v, w} N =
      augmentation.{u, v, w} M := by
  apply NatTrans.ext
  funext C
  apply Cat.Hom.ext
  change RetractWords.map (𝟭 C) h ⋙ RetractWords.augmentation C N = RetractWords.augmentation C M
  simpa only [CategoryTheory.Functor.comp_id] using RetractWords.map_augmentation (𝟭 C) h

def simplicialAugmentation (C : Cat.{max u v w, u}) :
    (simplicialFunctor.{u, max u v w, w}).obj C ⟶ (Functor.const _).obj C where
  app n := (RetractWords.augmentation C (WordSegment.degree.{w} n)).toCatHom
  naturality {_ _} θ := by
    apply Cat.Hom.ext
    change RetractWords.map (𝟭 C) (WordSegment.degreeMap θ) ⋙
      RetractWords.augmentation C _ = RetractWords.augmentation C _ ⋙ 𝟭 C
    exact RetractWords.map_augmentation (𝟭 C) (WordSegment.degreeMap θ)

def simplicialAugmentationNat : simplicialFunctor.{u, max u v w, w} ⟶
    (Functor.const SimplexCategoryᵒᵖ : Cat.{max u v w, u} ⥤ _) where
  app := simplicialAugmentation.{u, v, w}
  naturality {_ _} F := by
    apply NatTrans.ext
    funext n
    apply Cat.Hom.ext
    change RetractWords.map F.toFunctor (MonoidWithZeroHom.id (WordSegment.degree.{w} n)) ⋙
      RetractWords.augmentation _ _ = RetractWords.augmentation _ _ ⋙ F.toFunctor
    exact RetractWords.map_augmentation F.toFunctor (MonoidWithZeroHom.id _)

def bisimplicialAugmentation (A : SimplicialObject Cat.{max u v w, u}) :
    bisimplicial.{u, max u v w, w} A ⟶ A ⋙ Functor.const SimplexCategoryᵒᵖ :=
  CategoryTheory.Functor.whiskerLeft A (simplicialAugmentationNat.{u, v, w})

def diagonal (A : SimplicialObject Cat.{v, u}) : SimplicialObject Cat.{max u v w, u} :=
  Functor.diag _ ⋙ Functor.uncurry.obj (bisimplicial.{u, v, w} A)

def diagonalConstIso (A : SimplicialObject Cat.{v, u}) :
    Functor.diag SimplexCategoryᵒᵖ ⋙
      Functor.uncurry.obj (A ⋙ Functor.const SimplexCategoryᵒᵖ) ≅ A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change (A.map θ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ A.map θ
    simp)

def diagonalAugmentation (A : SimplicialObject Cat.{max u v w, u}) :
    diagonal.{u, max u v w, w} A ⟶ A :=
  CategoryTheory.Functor.whiskerLeft (Functor.diag _)
    (Functor.uncurry.map (bisimplicialAugmentation.{u, v, w} A)) ≫
    (diagonalConstIso A).hom

end SerrePositivity.SimplicialModel.WordPresentationAugmentation
