module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricInputCoordinates
public import SerrePositivity.KST.Spectra.SignedAdjointParametricFirstPost
public import SerrePositivity.KST.Spectra.SignedAdjointInputBoundary
public import SerrePositivity.KST.Spectra.InitialBoundarySquarePasting

/-!
概要：同じ交換符号辺の全族移送と実入力比較を貼り、元の第一辺の全族自然性を構成する。
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
variable {P A A' Y Y' Z Z' W W' B : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : P ⟶ PointedObject.basedHom Z Z')
  (w : P ⟶ PointedObject.basedHom W W')
  (hc : a ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u} w =
    PointedMapping.transpose v ≫ PointedObject.basedHomMap P a')
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ PointedObject.basedHom P A')
  {p : PointedObject.basedHom P (doubleLoop Z') ⟶ B}
  (H : PointedMapping.VerticalPath p (input f g ≫ doubleParametricPost v) (j ≫
    PointedObject.basedHomMap P (input f' g')))

local instance firstParametricNaturalityInnerKan :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance firstParametricNaturalityTargetKan : KanComplex (target Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance firstParametricNaturalityParameterKan :
    KanComplex (PointedObject.basedHom P (target Z')).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance firstParametricNaturalityHomKan : KanComplex (PointedObject.basedHom A
  (PointedObject.basedHom P (target Z'))).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 移送自然性と同じ実入力比較の二正方形・相対合成三角形を保持する貼り合わせ。 -/
def firstPathParametricNaturalityPasting :
    SquareAdjustment.InitialBoundaryPasting
      (firstPathParametricPostNaturalitySquare a ha a' ha' v w hc f g)
      (PointedMapping.VerticalPath.inputSquare H
        (((cancellationFirst a' ha').basedIhomMap P).basedPost (PointedObject.basedHomMap P
          (projection Z')))) :=
  SquareAdjustment.InitialBoundaryPasting.choose
    (firstPathParametricPostNaturalitySquare a ha a' ha' v w hc f g)
    (PointedMapping.VerticalPath.inputSquare H
      (((cancellationFirst a' ha').basedIhomMap P).basedPost (PointedObject.basedHomMap P
        (projection Z')))) _ _
    (firstPathParametricPostNaturalitySquare_start a ha a' ha' v w hc f g)
    (firstPathParametricPostNaturalitySquare_finish a ha a' ha' v w hc f g)

/-- 元の第一辺の前後合成を、同じ実入力比較と指定射影付きで結ぶ実自然性正方形。 -/
def firstPathParametricNaturalitySquare :
    SSet.Homotopy (((firstPath a ha f g).basedPost (targetParametricPost v)).path)
      ((((firstPath a' ha' f' g').basedIhomMap P).pre j).path) := by
  let C := firstPathParametricNaturalityPasting a ha a' ha' v w hc f g f' g' j H
  exact {
    h := C.homotopy.h
    h₀ := C.homotopy.h₀
    h₁ := C.homotopy.h₁.trans (firstPath_ihom_pre_path a' ha' f' g' j).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は、後半の同じ実入力正方形の非定値な左境界そのもの。 -/
lemma firstPathParametricNaturalitySquare_left :
    SquareAdjustment.leftSide ≫ (firstPathParametricNaturalitySquare a ha a' ha' v w hc f g f'
      g' j H).h =
      SquareAdjustment.leftSide ≫ (PointedMapping.VerticalPath.inputSquare H
        (((cancellationFirst a' ha').basedIhomMap P).basedPost (PointedObject.basedHomMap P
          (projection Z')))).h :=
  SquareAdjustment.InitialBoundaryPasting.left _ _
    (firstPathParametricNaturalityPasting a ha a' ha' v w hc f g f' g' j H)

/-- 右境界全体も、後半の同じ実入力正方形の非定値な右境界そのもの。 -/
lemma firstPathParametricNaturalitySquare_right :
    SquareAdjustment.rightSide ≫ (firstPathParametricNaturalitySquare a ha a' ha' v w hc f g f'
      g' j H).h =
      SquareAdjustment.rightSide ≫ (PointedMapping.VerticalPath.inputSquare H
        (((cancellationFirst a' ha').basedIhomMap P).basedPost (PointedObject.basedHomMap P
          (projection Z')))).h :=
  SquareAdjustment.InitialBoundaryPasting.right _ _
    (firstPathParametricNaturalityPasting a ha a' ha' v w hc f g f' g' j H)

end SerrePositivity.KST.Spectra.SignedAdjointPaths
