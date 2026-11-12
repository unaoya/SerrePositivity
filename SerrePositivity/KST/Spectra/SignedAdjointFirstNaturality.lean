module

public import SerrePositivity.KST.Spectra.SignedAdjointFirstInputCoordinates
public import SerrePositivity.KST.Spectra.SignedAdjointInputBoundary
public import SerrePositivity.KST.Spectra.InitialBoundarySquarePasting

/-!
概要：同じ交換符号辺の移送自然性と実入力比較を貼り、元の第一辺の自然性を構成する。
方針：前半の境界が定数であることを使い、後半の非定値な左右境界を全体で保持する。
規約：元の二正方形と相対合成三角形を保持。使われ方：実単位三角形の二辺の高次比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths
variable {A A' Y Y' Z Z' W W' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : Z ⟶ Z') (w : W ⟶ W')
  (hc : a ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} w = v ≫ a')
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ A') {p : doubleLoop Z' ⟶ B}
  (H : PointedMapping.VerticalPath p (input f g ≫ doublePost v) (j ≫ input f' g'))

local instance firstNaturalityInnerKan :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance firstNaturalityTargetKan : KanComplex (target Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance firstNaturalityHomKan : KanComplex (PointedObject.basedHom A (target Z')).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 移送自然性と同じ実入力比較の二正方形・相対合成三角形を保持する貼り合わせ。 -/
def firstPathNaturalityPasting :
    SquareAdjustment.InitialBoundaryPasting
      (firstPathPostNaturalitySquare a ha a' ha' v w hc f g)
      (PointedMapping.VerticalPath.inputSquare H
        ((cancellationFirst a' ha').basedPost (projection Z'))) :=
  SquareAdjustment.InitialBoundaryPasting.choose
    (firstPathPostNaturalitySquare a ha a' ha' v w hc f g)
    (PointedMapping.VerticalPath.inputSquare H
      ((cancellationFirst a' ha').basedPost (projection Z'))) _ _
    (firstPathPostNaturalitySquare_start a ha a' ha' v w hc f g)
    (firstPathPostNaturalitySquare_finish a ha a' ha' v w hc f g)

/-- 元の第一辺の前後合成を、同じ実入力比較と指定射影付きで結ぶ実自然性正方形。 -/
def firstPathNaturalitySquare :
    SSet.Homotopy (((firstPath a ha f g).basedPost (targetPost v)).path)
      (((firstPath a' ha' f' g').pre j).path) := by
  let C := firstPathNaturalityPasting a ha a' ha' v w hc f g f' g' j H
  exact {
    h := C.homotopy.h
    h₀ := C.homotopy.h₀
    h₁ := C.homotopy.h₁.trans (firstPath_pre_path a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は、後半の同じ実入力正方形の非定値な左境界そのもの。 -/
lemma firstPathNaturalitySquare_left :
    SquareAdjustment.leftSide ≫ (firstPathNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫ (PointedMapping.VerticalPath.inputSquare H
        ((cancellationFirst a' ha').basedPost (projection Z'))).h :=
  SquareAdjustment.InitialBoundaryPasting.left _ _
    (firstPathNaturalityPasting a ha a' ha' v w hc f g f' g' j H)

/-- 右境界全体も、後半の同じ実入力正方形の非定値な右境界そのもの。 -/
lemma firstPathNaturalitySquare_right :
    SquareAdjustment.rightSide ≫ (firstPathNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.rightSide ≫ (PointedMapping.VerticalPath.inputSquare H
        ((cancellationFirst a' ha').basedPost (projection Z'))).h :=
  SquareAdjustment.InitialBoundaryPasting.right _ _
    (firstPathNaturalityPasting a ha a' ha' v w hc f g f' g' j H)

/-- 元の二辺の実自然性正方形は、同じ非定値な中間境界を全区間で共有する。 -/
lemma firstSecondNaturalitySquare_shared :
    SquareAdjustment.rightSide ≫ (firstPathNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.leftSide ≫ (secondPathNaturalitySquare f g f' g' j v H).h :=
  (firstPathNaturalitySquare_right a ha a' ha' v w hc f g f' g' j H).trans
    (firstSecondInputSquare_shared f g f' g' j v H a' ha')

end SerrePositivity.KST.Spectra.SignedAdjointPaths
