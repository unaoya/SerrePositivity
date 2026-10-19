module

public import SerrePositivity.KST.Spectra.ExponentialSpecifiedComposition
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：上下の二つの実合成三角形を指定し、二つの正方形を同じ二単体族の上で貼り合わせる。
方針：両端境界上に元の二単体を束ね、指数写像空間の内二次元ホーンを相対充填する。
規約：上下の三角形を選び直さない。使われ方：段座標の同じ合成区間の段間整合性。
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
  (H : SSet.Homotopy f g) (V : SSet.Homotopy g k)
  (t₀ t₁ : (Δ[2] : SSet.{u}) ⟶ E)

/-- 上下の指定二単体を両端境界で保持する、元の二つの正方形の合成データ。 -/
abbrev SpecifiedPasting :=
  ExponentialPaths.SpecifiedComposite (boundary 1).ι H V
    (curry (intervalBoundaryFamily t₀ t₁))

/-- 元の四つの実辺が指定三角形の二辺なら、同じ上下三角形を保って貼り合わせる。 -/
def SpecifiedPasting.choose [KanComplex E]
    (hH₀ : leftSide ≫ H.h = stdSimplex.δ (2 : Fin 3) ≫ t₀)
    (hH₁ : rightSide ≫ H.h = stdSimplex.δ (2 : Fin 3) ≫ t₁)
    (hV₀ : leftSide ≫ V.h = stdSimplex.δ (0 : Fin 3) ≫ t₀)
    (hV₁ : rightSide ≫ V.h = stdSimplex.δ (0 : Fin 3) ≫ t₁) :
    SpecifiedPasting H V t₀ t₁ := by
  apply ExponentialPaths.SpecifiedComposite.choose
  · rw [curry_pre_app, ← curry_natural_left, intervalBoundaryFamily_pre,
      boundary_restriction, hH₀, hH₁]
  · rw [curry_pre_app, ← curry_natural_left, intervalBoundaryFamily_pre,
      boundary_restriction, hV₀, hV₁]

variable (C : SpecifiedPasting H V t₀ t₁)

/-- 合成区間の両端制限は、指定した同じ上下三角形の対角辺の族。 -/
lemma SpecifiedPasting.boundary :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h =
      intervalBoundaryFamily (stdSimplex.δ (1 : Fin 3) ≫ t₀)
        (stdSimplex.δ (1 : Fin 3) ≫ t₁) := by
  have h := C.restriction
  rw [← curry_natural_left, intervalBoundaryFamily_pre, uncurry_curry] at h
  exact h

/-- 元の向きに戻した正方形は、指定した二つの対角区間の間の実ホモトピー。 -/
def SpecifiedPasting.squareHomotopy : SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ t₀)
    (stdSimplex.δ (1 : Fin 3) ≫ t₁) :=
  homotopyOfBoundaryRestriction (E := E) C.homotopy.h (SpecifiedPasting.boundary H V t₀ t₁ C)

/-- 合成正方形の左辺は、入力した元の最初の辺そのもの。 -/
lemma SpecifiedPasting.square_left :
    leftSide ≫ (SpecifiedPasting.squareHomotopy H V t₀ t₁ C).h = f :=
  (leftSide_swap C.homotopy.h).trans C.homotopy.h₀

/-- 合成正方形の右辺も、入力した元の最後の辺そのもの。 -/
lemma SpecifiedPasting.square_right :
    rightSide ≫ (SpecifiedPasting.squareHomotopy H V t₀ t₁ C).h = k :=
  (rightSide_swap C.homotopy.h).trans C.homotopy.h₁

end SerrePositivity.KST.Spectra.SquareAdjustment
