module

public import SerrePositivity.InfinityCategories.Stable.Pointed

/-!
概要：正方形の転置と四辺の制限の交換。
方針：図式を展開せず、二座標の形状の恒等式だけを使う。
規約：任意の値域と実正方形を保持。使われ方：大きな coherent 図式の辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X : SSet.{u}} (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)

lemma square_transpose_bottom :
    squareBottomEdge ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ S) = squareLeftEdge ≫ S := rfl

lemma square_transpose_right :
    squareRightEdge ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ S) = squareTopEdge ≫ S := rfl

lemma square_transpose_left :
    squareLeftEdge ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ S) = squareBottomEdge ≫ S := rfl

lemma square_transpose_top :
    squareTopEdge ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ S) = squareRightEdge ≫ S := rfl

end SerrePositivity.KST.LocalizingInvariants
