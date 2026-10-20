module

public import SerrePositivity.KST.Spectra.SquareTransposition
public import SerrePositivity.KST.Spectra.SpecifiedSquareDifference

/-!
概要：共通始点の二辺の実自然性から、指定した逆向き三角形の残る辺を比較する。
方針：同じ始点境界で正方形を転置して相対外ホーンを充填し、元の向きへ戻す。
規約：非定値な共有境界と選択済みの三角形を保持。使われ方：単位構造の逆区間の比較。
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
  (hm : leftSide ≫ H.h = leftSide ≫ V.h)
  (t₀ t₁ : (Δ[2] : SSet.{u}) ⟶ E)

/-- 元の二つの正方形と二つの実逆三角形を保持する、転置した相対外ホーンの充填。 -/
abbrev TriangleEdgeDifference := SpecifiedDifference (transpose H)
  (transposeWithEndpoints V hm rfl) t₀ t₁

/-- 実際の二辺が指定逆三角形の辺なら、同じ二単体を固定して比較を構成する。 -/
def TriangleEdgeDifference.choose [KanComplex E]
    (hp₀ : stdSimplex.δ (2 : Fin 3) ≫ t₀ = p₀)
    (hp₁ : stdSimplex.δ (2 : Fin 3) ≫ t₁ = p₁)
    (hq₀ : stdSimplex.δ (1 : Fin 3) ≫ t₀ = q₀)
    (hq₁ : stdSimplex.δ (1 : Fin 3) ≫ t₁ = q₁) :
    TriangleEdgeDifference H V hm t₀ t₁ :=
  SpecifiedDifference.choose (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁
    ((transpose_left H).trans hp₀.symm) ((transpose_right H).trans hp₁.symm)
    ((transpose_left V).trans hq₀.symm) ((transpose_right V).trans hq₁.symm)

variable (C : TriangleEdgeDifference H V hm t₀ t₁)

/-- 元の二つの指定逆三角形の第二辺の間の実自然性正方形。 -/
def TriangleEdgeDifference.square :
    SSet.Homotopy (stdSimplex.δ (0 : Fin 3) ≫ t₀) (stdSimplex.δ (0 : Fin 3) ≫ t₁) :=
  SpecifiedDifference.squareHomotopy (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁ C

/-- 左辺全体は元の合成辺の正方形の右辺そのもの。 -/
lemma TriangleEdgeDifference.left :
    leftSide ≫ (TriangleEdgeDifference.square H V hm t₀ t₁ C).h = rightSide ≫ H.h :=
  SpecifiedDifference.square_left (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁ C

/-- 右辺全体も元の定数辺の正方形の右辺そのもの。 -/
lemma TriangleEdgeDifference.right :
    rightSide ≫ (TriangleEdgeDifference.square H V hm t₀ t₁ C).h = rightSide ≫ V.h :=
  SpecifiedDifference.square_right (transpose H) (transposeWithEndpoints V hm rfl) t₀ t₁ C

end SerrePositivity.KST.Spectra.SquareAdjustment
