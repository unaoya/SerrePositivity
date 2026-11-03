module

public import SerrePositivity.KST.LocalizingInvariants.IntervalPrecompositionFamily
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.Pullback

/-!
概要：実正方形を、その縦方向の二辺を対象とする区間関手の族へ移す。
方針：座標を交換して curry し、四辺への制限を厳密に保持する。
規約：普遍性の仮定は不要。使われ方：Ore pullback の右脚の族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def squareArrowFamily {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ R)

lemma squareArrowFamily_source {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    squareArrowFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      squareBottomEdge ≫ R := by
  rw [squareArrowFamily, curry_evaluateFunctorAt_interval, ← Category.assoc]
  rfl

lemma squareArrowFamily_target {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    squareArrowFamily R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      squareTopEdge ≫ R := by
  rw [squareArrowFamily, curry_evaluateFunctorAt_interval, ← Category.assoc]
  rfl

lemma squareArrowFamily_one {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    stdSimplex.δ (0 : Fin 2) ≫ squareArrowFamily R =
      SSet.const (functorVertex (squareRightEdge ≫ R)) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  change ((ihom (Δ[1] : SSet.{u})).obj X).δ 0
    (SSet.yonedaEquiv (curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ R))) =
      PinchedHom.constant (functorVertex (squareRightEdge ≫ R)) 0
  rw [pinchedConstant_zero, ← functorVertex_uncurry_one, Equiv.symm_apply_apply, uncurry_curry]
  rfl

lemma squareArrowFamily_zero {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    stdSimplex.δ (1 : Fin 2) ≫ squareArrowFamily R =
      SSet.const (functorVertex (squareLeftEdge ≫ R)) := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  change ((ihom (Δ[1] : SSet.{u})).obj X).δ 1
    (SSet.yonedaEquiv (curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ R))) =
      PinchedHom.constant (functorVertex (squareLeftEdge ≫ R)) 0
  rw [pinchedConstant_zero, ← functorVertex_uncurry_zero, Equiv.symm_apply_apply, uncurry_curry]
  rfl

end SerrePositivity.KST.LocalizingInvariants
