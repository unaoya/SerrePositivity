module

public import SerrePositivity.KST.Spectra.ExponentialSpecifiedDifference
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：上下の実比較三角形を指定し、共有辺を持つ二つの正方形の終辺を比較する。
方針：両端境界上に元の二単体を束ね、指数写像空間の外二次元ホーンを相対充填する。
規約：上下の三角形を選び直さない。使われ方：段座標の同じ比較区間の段間整合性。
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
  (H : SSet.Homotopy f g) (V : SSet.Homotopy f k)
  (t₀ t₁ : (Δ[2] : SSet.{u}) ⟶ E)

/-- 上下の指定二単体を両端境界で保持する、元の二つの正方形の比較データ。 -/
abbrev SpecifiedDifference :=
  ExponentialPaths.SpecifiedDifference (boundary 1).ι H V
    (curry (intervalBoundaryFamily t₀ t₁))

/-- 元の四つの実辺が指定三角形の二辺なら、同じ上下三角形を保って比較する。 -/
def SpecifiedDifference.choose [KanComplex E]
    (hH₀ : leftSide ≫ H.h = stdSimplex.δ (2 : Fin 3) ≫ t₀)
    (hH₁ : rightSide ≫ H.h = stdSimplex.δ (2 : Fin 3) ≫ t₁)
    (hV₀ : leftSide ≫ V.h = stdSimplex.δ (1 : Fin 3) ≫ t₀)
    (hV₁ : rightSide ≫ V.h = stdSimplex.δ (1 : Fin 3) ≫ t₁) :
    SpecifiedDifference H V t₀ t₁ := by
  apply ExponentialPaths.SpecifiedDifference.choose
  · rw [curry_pre_app, ← curry_natural_left, intervalBoundaryFamily_pre,
      boundary_restriction, hH₀, hH₁]
  · rw [curry_pre_app, ← curry_natural_left, intervalBoundaryFamily_pre,
      boundary_restriction, hV₀, hV₁]

variable (C : SpecifiedDifference H V t₀ t₁)

/-- 比較区間の両端制限は、指定した同じ上下三角形の第二辺の族。 -/
lemma SpecifiedDifference.boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h =
      intervalBoundaryFamily (stdSimplex.δ (0 : Fin 3) ≫ t₀)
        (stdSimplex.δ (0 : Fin 3) ≫ t₁) := by
  have h := C.restriction
  rw [← curry_natural_left, intervalBoundaryFamily_pre, uncurry_curry] at h
  exact h

/-- 元の向きに戻した正方形は、指定した二つの対角区間の間の実ホモトピー。 -/
def SpecifiedDifference.squareHomotopy : SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ t₀)
    (stdSimplex.δ (0 : Fin 3) ≫ t₁) :=
  homotopyOfBoundaryRestriction (E := E) C.homotopy.h (SpecifiedDifference.boundary H V t₀ t₁ C)

/-- 合成正方形の左辺は、入力した元の第一の終辺そのもの。 -/
lemma SpecifiedDifference.square_left :
    leftSide ≫ (SpecifiedDifference.squareHomotopy H V t₀ t₁ C).h = g :=
  (leftSide_swap C.homotopy.h).trans C.homotopy.h₀

/-- 合成正方形の右辺も、入力した元の第二の終辺そのもの。 -/
lemma SpecifiedDifference.square_right :
    rightSide ≫ (SpecifiedDifference.squareHomotopy H V t₀ t₁ C).h = k :=
  (rightSide_swap C.homotopy.h).trans C.homotopy.h₁

end SerrePositivity.KST.Spectra.SquareAdjustment
