module

public import SerrePositivity.KST.Spectra.ExponentialSpecifiedCodifference
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：上下の同じ実比較三角形を指定し、共通終辺を持つ正方形の始辺を比較する。
方針：指数写像空間での相対外ホーン充填から、元の向きの実正方形を回収する。
規約：上下三角形を再選択しない。使われ方：実評価から源単位比較への段間整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment
variable {E : SSet.{u}} {f g k : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy f k) (V : SSet.Homotopy g k)
  (t₀ t₁ : (Δ[2] : SSet.{u}) ⟶ E)

/-- 共通終点の二つの正方形の上下で、指定三角形を全体として保持する比較。 -/
abbrev SpecifiedCodifference :=
  ExponentialPaths.SpecifiedCodifference (boundary 1).ι H V
    (curry (intervalBoundaryFamily t₀ t₁))

/-- 元の四辺が指定三角形の二辺なら、同じ上下三角形を保って始辺を比較する。 -/
def SpecifiedCodifference.choose [KanComplex E]
    (hH₀ : leftSide ≫ H.h = stdSimplex.δ (1 : Fin 3) ≫ t₀)
    (hH₁ : rightSide ≫ H.h = stdSimplex.δ (1 : Fin 3) ≫ t₁)
    (hV₀ : leftSide ≫ V.h = stdSimplex.δ (0 : Fin 3) ≫ t₀)
    (hV₁ : rightSide ≫ V.h = stdSimplex.δ (0 : Fin 3) ≫ t₁) :
    SpecifiedCodifference H V t₀ t₁ := by
  apply ExponentialPaths.SpecifiedCodifference.choose
  · rw [curry_pre_app, ← curry_natural_left, intervalBoundaryFamily_pre,
      boundary_restriction, hH₀, hH₁]
  · rw [curry_pre_app, ← curry_natural_left, intervalBoundaryFamily_pre,
      boundary_restriction, hV₀, hV₁]

variable (C : SpecifiedCodifference H V t₀ t₁)

/-- 比較区間の両端制限は、同じ指定三角形の第一辺の族。 -/
lemma SpecifiedCodifference.boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h =
      intervalBoundaryFamily (stdSimplex.δ (2 : Fin 3) ≫ t₀)
        (stdSimplex.δ (2 : Fin 3) ≫ t₁) := by
  have h := C.restriction
  rw [← curry_natural_left, intervalBoundaryFamily_pre, uncurry_curry] at h
  exact h

/-- 元の向きの実正方形は、上下に指定した同じ二つの比較辺を結ぶ。 -/
def SpecifiedCodifference.squareHomotopy : SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ t₀)
    (stdSimplex.δ (2 : Fin 3) ≫ t₁) :=
  homotopyOfBoundaryRestriction (E := E) C.homotopy.h (SpecifiedCodifference.boundary H V t₀ t₁ C)

/-- 左辺全体は元の第一の始辺そのもの。 -/
lemma SpecifiedCodifference.square_left :
    leftSide ≫ (SpecifiedCodifference.squareHomotopy H V t₀ t₁ C).h = f :=
  (leftSide_swap C.homotopy.h).trans C.homotopy.h₀

/-- 右辺全体も元の第二の始辺そのもの。 -/
lemma SpecifiedCodifference.square_right :
    rightSide ≫ (SpecifiedCodifference.squareHomotopy H V t₀ t₁ C).h = g :=
  (rightSide_swap C.homotopy.h).trans C.homotopy.h₁

end SerrePositivity.KST.Spectra.SquareAdjustment
