module

public import SerrePositivity.KST.Spectra.SignedAdjointNaturalityCoordinates

/-!
概要：元の二重反転辺の自然性を、実際の二重 loop 入力の比較区間から構成する。
方針：同じ普遍反転区間へ入力比較を作用させ、元の第二辺の前後合成へ照合する。
規約：入力の厳密自然性を要求せず、非定値な左右境界を全体で保持する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths
variable {A A' Y Y' Z Z' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right]
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ A') (v : Z ⟶ Z') {p : doubleLoop Z' ⟶ B}
  (H : PointedMapping.VerticalPath p (input f g ≫ doublePost v) (j ≫ input f' g'))

/-- 実入力比較を使う第二辺の自然性。二次元射は元の入力正方形そのもの。 -/
def secondPathNaturalitySquare :
    SSet.Homotopy (((secondPath f g).basedPost (targetPost v)).path)
      (((secondPath f' g').pre j).path) := by
  let P := (reversalTwice Z').basedPost (projection Z')
  let S := PointedMapping.VerticalPath.inputSquare H P
  exact {
    h := S.h
    h₀ := (S.h₀.trans ((reversalTwice Z').pre_basedPost_path
      (input f g ≫ doublePost v) (projection Z'))).trans (secondPath_post_path f g v).symm
    h₁ := (S.h₁.trans ((reversalTwice Z').pre_basedPost_path
      (j ≫ input f' g') (projection Z'))).trans (secondPath_pre_path f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は、実入力比較を同じ二重反転・射影の頂点へ作用させた区間。 -/
lemma secondPathNaturalitySquare_left :
    SquareAdjustment.leftSide ≫ (secondPathNaturalitySquare f g f' g' j v H).h =
      lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
        (PointedMapping.pointFamily ((reversal Z' ≫ reversal Z') ≫ projection Z') ▷
          (Δ[1] : SSet.{u})) ≫ (H.forgetProjection.basedPre (target Z')).homotopy.h :=
  PointedMapping.VerticalPath.inputSquare_left H ((reversalTwice Z').basedPost (projection Z'))

/-- 右境界全体も、同じ実入力比較を元の射影の頂点へ作用させた区間。 -/
lemma secondPathNaturalitySquare_right :
    SquareAdjustment.rightSide ≫ (secondPathNaturalitySquare f g f' g' j v H).h =
      lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
        (PointedMapping.pointFamily (𝟙 (doubleLoop Z') ≫ projection Z') ▷
          (Δ[1] : SSet.{u})) ≫ (H.forgetProjection.basedPre (target Z')).homotopy.h :=
  PointedMapping.VerticalPath.inputSquare_right H ((reversalTwice Z').basedPost (projection Z'))

end SerrePositivity.KST.Spectra.SignedAdjointPaths
