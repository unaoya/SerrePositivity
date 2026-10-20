module

public import SerrePositivity.KST.Spectra.TriangleEdgePasting
public import SerrePositivity.KST.Spectra.TriangleEdgeDifference

/-!
概要：実合成三角形と実逆三角形の組を保持し、元の逆区間の高次比較を構成する。
方針：二辺の正方形を指定合成三角形で貼り、同じ対角辺と指定逆三角形で比較する。
規約：四つの三角形と三つの入力正方形を保持。使われ方：単位構造の実逆区間の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment

/-- 同じ対角辺を共有する、選択済みの合成・逆向き二単体。 -/
structure TrianglePair (E : SSet.{u}) where
  forward : (Δ[2] : SSet.{u}) ⟶ E
  inverse : (Δ[2] : SSet.{u}) ⟶ E
  shared : stdSimplex.δ (1 : Fin 3) ≫ forward = stdSimplex.δ (2 : Fin 3) ≫ inverse

/-- 同じ二つの三角形を一つの射で写しても、共有辺は実辺全体で一致する。 -/
def TrianglePair.map {E F : SSet.{u}} (T : TrianglePair E) (m : E ⟶ F) : TrianglePair F where
  forward := T.forward ≫ m
  inverse := T.inverse ≫ m
  shared := by simpa only [Category.assoc] using congrArg (· ≫ m) T.shared

variable {E : SSet.{u}} (T₀ T₁ : TrianglePair E)
  (H : SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ T₀.forward)
    (stdSimplex.δ (2 : Fin 3) ≫ T₁.forward))
  (V : SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ T₀.forward)
    (stdSimplex.δ (0 : Fin 3) ≫ T₁.forward))
  (U : SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ T₀.inverse)
    (stdSimplex.δ (1 : Fin 3) ≫ T₁.inverse))
  (hm : rightSide ≫ H.h = leftSide ≫ V.h)
  (hl : leftSide ≫ H.h = leftSide ≫ U.h)

/-- 三つの元の正方形を、同じ四つの三角形で比較した実相対ホーンのデータ。 -/
structure TrianglePairComparison where
  forward : TriangleEdgePasting H V hm T₀.forward T₁.forward
  inverse : TriangleEdgeDifference
    (TriangleEdgePasting.square H V hm T₀.forward T₁.forward forward) U
    ((TriangleEdgePasting.left H V hm T₀.forward T₁.forward forward).trans hl)
    T₀.inverse T₁.inverse

/-- 合成・逆三角形を選び直さず、元の二段の相対ホーンを充填する。 -/
def TrianglePairComparison.choose [KanComplex E] : TrianglePairComparison T₀ T₁ H V U hm hl := by
  let F := TriangleEdgePasting.choose H V hm T₀.forward T₁.forward rfl rfl rfl rfl
  exact ⟨F, TriangleEdgeDifference.choose
    (TriangleEdgePasting.square H V hm T₀.forward T₁.forward F) U
    ((TriangleEdgePasting.left H V hm T₀.forward T₁.forward F).trans hl)
    T₀.inverse T₁.inverse T₀.shared.symm T₁.shared.symm rfl rfl⟩

variable (C : TrianglePairComparison T₀ T₁ H V U hm hl)

/-- 同じ指定逆三角形の残る辺の間の実自然性正方形。 -/
def TrianglePairComparison.square :
    SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ T₀.inverse)
      (stdSimplex.δ (0 : Fin 3) ≫ T₁.inverse) :=
  TriangleEdgeDifference.square
    (TriangleEdgePasting.square H V hm T₀.forward T₁.forward C.forward) U
    ((TriangleEdgePasting.left H V hm T₀.forward T₁.forward C.forward).trans hl)
    T₀.inverse T₁.inverse C.inverse

/-- 左境界は元の第二辺の正方形の終境界全体。 -/
lemma TrianglePairComparison.left :
    leftSide ≫ (TrianglePairComparison.square T₀ T₁ H V U hm hl C).h = rightSide ≫ V.h :=
  (TriangleEdgeDifference.left _ _ _ _ _ C.inverse).trans
    (TriangleEdgePasting.right H V hm T₀.forward T₁.forward C.forward)

/-- 右境界は元の第三正方形の終境界全体。 -/
lemma TrianglePairComparison.right :
    rightSide ≫ (TrianglePairComparison.square T₀ T₁ H V U hm hl C).h = rightSide ≫ U.h :=
  TriangleEdgeDifference.right _ _ _ _ _ C.inverse

end SerrePositivity.KST.Spectra.SquareAdjustment
