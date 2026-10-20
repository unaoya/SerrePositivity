module

public import SerrePositivity.KST.Spectra.SquareTransposition
public import SerrePositivity.KST.Spectra.SpecifiedSquarePasting

/-!
概要：二辺の実自然性正方形から、指定した二つの合成三角形の対角辺を比較する。
方針：同じ中間境界で正方形を転置して貼り合わせ、元の向きへ戻す。
規約：非定値な共有境界と選択済みの三角形を保持。使われ方：単位構造の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SquareAdjustment
variable {E : SSet.{u}} {p₀ p₁ q₀ q₁ : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy p₀ p₁) (V : SSet.Homotopy q₀ q₁)
  (hm : rightSide ≫ H.h = leftSide ≫ V.h)
  (t₀ t₁ : (Δ[2] : SSet.{u}) ⟶ E)

/-- 元の二つの正方形と二つの実三角形を保持する、転置した相対内ホーンの充填。 -/
abbrev TriangleEdgePasting := SpecifiedPasting (transpose H)
  (transposeWithEndpoints V hm rfl) t₀ t₁

/-- 実際の二辺が指定合成三角形の辺なら、同じ二単体を固定して比較を構成する。 -/
def TriangleEdgePasting.choose [KanComplex E]
    (hp₀ : stdSimplex.δ (2 : Fin 3) ≫ t₀ = p₀)
    (hp₁ : stdSimplex.δ (2 : Fin 3) ≫ t₁ = p₁)
    (hq₀ : stdSimplex.δ (0 : Fin 3) ≫ t₀ = q₀)
    (hq₁ : stdSimplex.δ (0 : Fin 3) ≫ t₁ = q₁) :
    TriangleEdgePasting H V hm t₀ t₁ :=
  SpecifiedPasting.choose (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁
    ((transpose_left H).trans hp₀.symm) ((transpose_right H).trans hp₁.symm)
    ((transpose_left V).trans hq₀.symm) ((transpose_right V).trans hq₁.symm)

variable (C : TriangleEdgePasting H V hm t₀ t₁)

/-- 元の二つの指定合成三角形の対角辺の間の実自然性正方形。 -/
def TriangleEdgePasting.square :
    SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ t₀) (stdSimplex.δ (1 : Fin 3) ≫ t₁) :=
  SpecifiedPasting.squareHomotopy (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁ C

/-- 左辺全体は元の第一正方形の左辺そのもの。 -/
lemma TriangleEdgePasting.left :
    leftSide ≫ (TriangleEdgePasting.square H V hm t₀ t₁ C).h = leftSide ≫ H.h :=
  SpecifiedPasting.square_left (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁ C

/-- 右辺全体も元の第二正方形の右辺そのもの。 -/
lemma TriangleEdgePasting.right :
    rightSide ≫ (TriangleEdgePasting.square H V hm t₀ t₁ C).h = rightSide ≫ V.h :=
  SpecifiedPasting.square_right (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁ C

end SerrePositivity.KST.Spectra.SquareAdjustment
