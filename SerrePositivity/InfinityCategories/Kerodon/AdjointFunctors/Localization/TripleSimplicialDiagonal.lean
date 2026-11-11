module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialDiagonal

/-!
# 三重単体集合の元の部分対角と全対角

概要：外側とラベル次数を先に対角にしても、元の三重全対角と同型。
方針：同じ uncurry と対角への前合成を単体集合の圏で使う。
規約：同型の各成分は元の同じ単体の恒等射。
使われ方：DK10.6の射列長を固定した部分対角から全比較へ戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def partialDiagonalFunctor :
    SimplicialObject (SimplicialObject SSet.{u}) ⥤ SimplicialObject SSet.{u} :=
  CategoryTheory.Functor.uncurry ⋙
    (CategoryTheory.Functor.whiskeringLeft (C := SimplexCategoryᵒᵖ)
      (D := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (E := SSet.{u})).obj
        (CategoryTheory.Functor.diag SimplexCategoryᵒᵖ)

def fullDiagonalIso (B : SimplicialObject (SimplicialObject SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (partialDiagonalFunctor.obj B) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (B ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro n m θ; ext e; rfl)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
