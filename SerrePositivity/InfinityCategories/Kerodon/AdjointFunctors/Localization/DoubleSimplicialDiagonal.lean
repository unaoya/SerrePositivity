module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering

/-!
# 二重単体集合の元の対角

概要：二つの単体次数を同時に動かす対角関手と、定数図式の元の単体集合への同型。
方針：元の二変数の関手を uncurry し、単体圏の対角へ前合成する。
規約：全作用素と自然変換の対角成分を保持する。
使われ方：自由解像の hammock 図式の元の対角と augmentation。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def diagonalFunctor : SimplicialObject SSet.{u} ⥤ SSet.{u} :=
  CategoryTheory.Functor.uncurry ⋙
    (CategoryTheory.Functor.whiskeringLeft (C := SimplexCategoryᵒᵖ)
      (D := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (E := Type u)).obj
        (CategoryTheory.Functor.diag SimplexCategoryᵒᵖ)

lemma diagonalFunctor_obj_obj (B : SimplicialObject SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (diagonalFunctor.obj B).obj n = (B.obj n).obj n := rfl

lemma diagonalFunctor_obj_map (B : SimplicialObject SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (diagonalFunctor.obj B).map θ = (B.map θ).app n ≫ (B.obj m).map θ := rfl

lemma diagonalFunctor_map_app {B D : SimplicialObject SSet.{u}} (α : B ⟶ D)
    (n : SimplexCategoryᵒᵖ) : (diagonalFunctor.map α).app n = (α.app n).app n := rfl

def diagonalConstantIso (X : SSet.{u}) :
    diagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj X) ≅ X :=
  NatIso.ofComponents (fun n => Iso.refl (X.obj n)) (by
    intro n m θ
    change (𝟙 _ ≫ X.map θ) ≫ 𝟙 _ = 𝟙 _ ≫ X.map θ
    simp)

/-- 内側の次数が定数である二重単体集合の対角は元の外側の単体集合。 -/
def diagonalDiscreteIso (X : SSet.{u}) :
    diagonalFunctor.obj (X ⋙ Functor.const SimplexCategoryᵒᵖ) ≅ X :=
  NatIso.ofComponents (fun n => Iso.refl (X.obj n)) (by
    intro n m θ
    change (X.map θ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ X.map θ
    simp)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
