module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricSecondCoordinates
public import SerrePositivity.KST.Spectra.SignedAdjointParametricFirstNaturality

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
variable {P A A' Y Y' Z Z' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right]
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ PointedObject.basedHom P A') (v : P ⟶ PointedObject.basedHom Z Z')
  {p : PointedObject.basedHom P (doubleLoop Z') ⟶ B}
  (H : PointedMapping.VerticalPath p (input f g ≫ doubleParametricPost v) (j ≫
    PointedObject.basedHomMap P (input f' g')))

/-- 実入力比較を使う第二辺の自然性。二次元射は元の入力正方形そのもの。 -/
def secondPathParametricNaturalitySquare :
    SSet.Homotopy (((secondPath f g).basedPost (targetParametricPost v)).path)
      ((((secondPath f' g').basedIhomMap P).pre j).path) := by
  let R := ((reversalTwice Z').basedIhomMap P).basedPost (PointedObject.basedHomMap P
    (projection Z'))
  let S := PointedMapping.VerticalPath.inputSquare H R
  exact {
    h := S.h
    h₀ := (S.h₀.trans (((reversalTwice Z').basedIhomMap P).pre_basedPost_path
      (input f g ≫ doubleParametricPost v) (PointedObject.basedHomMap P (projection
        Z')))).trans (secondPath_parametric_post_path f g v).symm
    h₁ := S.h₁.trans (secondPath_ihom_pre_path f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は、同じ実入力正方形の左境界そのもの。 -/
lemma secondPathParametricNaturalitySquare_left :
    SquareAdjustment.leftSide ≫
        (secondPathParametricNaturalitySquare f g f' g' j v H).h =
      SquareAdjustment.leftSide ≫ (PointedMapping.VerticalPath.inputSquare H
        (((reversalTwice Z').basedIhomMap P).basedPost
          (PointedObject.basedHomMap P (projection Z')))).h := rfl

/-- 右境界全体も、同じ実入力正方形の右境界そのもの。 -/
lemma secondPathParametricNaturalitySquare_right :
    SquareAdjustment.rightSide ≫
        (secondPathParametricNaturalitySquare f g f' g' j v H).h =
      SquareAdjustment.rightSide ≫ (PointedMapping.VerticalPath.inputSquare H
        (((reversalTwice Z').basedIhomMap P).basedPost
          (PointedObject.basedHomMap P (projection Z')))).h := rfl

variable {W W' : PointedSimplicialSet.{u}} [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (w : P ⟶ PointedObject.basedHom W W')
  (hc : a ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u} w =
    PointedMapping.transpose v ≫ PointedObject.basedHomMap P a')

/-- 第一・第二辺の全族正方形は、同じ実入力の非定値な中間境界全体を共有する。 -/
lemma firstSecondParametricNaturalitySquare_shared :
    SquareAdjustment.rightSide ≫
        (firstPathParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫
        (secondPathParametricNaturalitySquare f g f' g' j v H).h := by
  rw [firstPathParametricNaturalitySquare_right, secondPathParametricNaturalitySquare_left,
    PointedMapping.VerticalPath.inputSquare_right, PointedMapping.VerticalPath.inputSquare_left]

end SerrePositivity.KST.Spectra.SignedAdjointPaths
