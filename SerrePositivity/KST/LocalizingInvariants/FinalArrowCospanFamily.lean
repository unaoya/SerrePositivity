module

public import SerrePositivity.KST.LocalizingInvariants.FinalHornArrowSquares
public import SerrePositivity.InfinityCategories.Stable.CospanFamilies

/-!
概要：基底単体の最後の頂点への収縮と、その点へ入る最後の矢印から全 cospan 族を作る。
方針：二脚の終点評価を厳密に一致させ、cospan の pushout で貼る。
規約：高次パラメーターを保持。使われ方：最終外ホーンの正方形族の延長の基底。
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

lemma simplexTargetContraction_endpoint {X : SSet.{u}} (n : ℕ) (β : (Δ[n] : SSet.{u}) ⟶ X) :
    curry (prismLastContraction n ≫ β) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SSet.const (β.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
  rw [curry_evaluateFunctorAt_interval, ← Category.assoc, prismLastContraction_one,
    SSet.const_comp]

def finalArrowCospanFamily {X : SSet.{u}} (n : ℕ) (β : (Δ[n] : SSet.{u}) ⟶ X)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌)
    (hv : (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
      (Opposite.op ⦋0⦌) v = β.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) :
    (Δ[n] : SSet.{u}) ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  stable_cospanFamilyOfArrows (curry (prismLastContraction n ≫ β)) (SSet.const v) (by
    rw [simplexTargetContraction_endpoint, SSet.const_comp, hv])

lemma finalArrowCospanFamily_left {X : SSet.{u}} (n : ℕ) (β : (Δ[n] : SSet.{u}) ⟶ X)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) (hv) :
    finalArrowCospanFamily n β v hv ≫ (pre horn₂₂.ι₀₂).app X =
      curry (prismLastContraction n ≫ β) := stable_cospanFamilyOfArrows_left _ _ _

lemma finalArrowCospanFamily_right {X : SSet.{u}} (n : ℕ) (β : (Δ[n] : SSet.{u}) ⟶ X)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) (hv) :
    finalArrowCospanFamily n β v hv ≫ (pre horn₂₂.ι₁₂).app X = SSet.const v :=
  stable_cospanFamilyOfArrows_right _ _ _

lemma finalArrowCospanFamily_base {X : SSet.{u}} (n : ℕ) (β : (Δ[n] : SSet.{u}) ⟶ X)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) (hv) :
    (finalArrowCospanFamily n β v hv ≫ (pre horn₂₂.ι₀₂).app X) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = β := by
  rw [finalArrowCospanFamily_left, curry_evaluateFunctorAt_interval,
    ← Category.assoc, prismLastContraction_zero, Category.id_comp]

lemma finalHorn_lastArrow_target {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (β : (Δ[m + 2] : SSet.{u}) ⟶ X)
    (hβ : σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ β) :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌)
      (σ.app (Opposite.op ⦋0⦌) (finalHornLastVertex m)) =
      β.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last (m + 2))) :=
  congrArg (fun k => k.app (Opposite.op ⦋0⦌) (finalHornLastVertex m)) hβ

lemma finalHornArrowSquares_cospan {X : SSet.{u}} (m : ℕ)
    (σ : (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (β : (Δ[m + 2] : SSet.{u}) ⟶ X)
    (hβ : σ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫ β) :
    finalHornArrowSquares m σ ≫ (pre cospanSquareBoundary).app X =
      (horn (m + 2) (Fin.last (m + 2))).ι ≫
        finalArrowCospanFamily (m + 2) β (σ.app (Opposite.op ⦋0⦌) (finalHornLastVertex m))
          (finalHorn_lastArrow_target m σ β hβ) := by
  apply stable_cospanFamily_hom_ext
  · simp only [Category.assoc, finalArrowCospanFamily_left]
    have hp : (pre cospanSquareBoundary).app X ≫ (pre horn₂₂.ι₀₂).app X =
        (pre squareRightEdge).app X := by
      rw [← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_rightEdge]
    rw [hp, finalHornArrowSquares_right m σ β hβ,
      ← curry_natural_left]
  · simp only [Category.assoc, finalArrowCospanFamily_right]
    have hp : (pre cospanSquareBoundary).app X ≫ (pre horn₂₂.ι₁₂).app X =
        (pre squareTopEdge).app X := by
      rw [← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_topEdge]
    rw [hp, finalHornArrowSquares_top, SSet.comp_const]

end SerrePositivity.KST.LocalizingInvariants
