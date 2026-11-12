module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricTriangleEdges

/-!
概要：元の三正方形と保存済み四三角形から、実際の逆向き随伴比較区間の自然性を構成する。
方針：指定した合成三角形の対角辺を比較し、同じ指定逆三角形の残る辺へ移す。
規約：元の実区間と非定値な全境界を保持。使われ方：単位構造の実逆区間の高次比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
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
  {p : PointedObject.basedHom P (LoopExchangePaths.doubleLoop Z') ⟶ B}
  (H : PointedMapping.VerticalPath p
    (input f g ≫ LoopExchangePaths.doubleParametricPost v) (j ≫ PointedObject.basedHomMap P
      (input f' g')))

local instance reverseParametricNaturalityInnerKan :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance reverseParametricNaturalityTargetKan : KanComplex (target Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance reverseParametricNaturalityParameterKan :
    KanComplex (PointedObject.basedHom P (target Z')).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance reverseParametricNaturalityHomKan : KanComplex (PointedObject.basedHom A
  (PointedObject.basedHom P (target Z'))).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の三自然性正方形と保存済み四つの実三角形を保持する、二段の相対ホーン比較。 -/
def reverseParametricNaturalityComparison :=
  SquareAdjustment.TrianglePairComparison.choose
    (parametricPostTrianglePair a ha f g v) (parametricPreTrianglePair a' ha' f' g' j)
    (triangleFirstParametricNaturalitySquare a ha a' ha' v w hc f g f' g' j H)
    (triangleSecondParametricNaturalitySquare a ha a' ha' v f g f' g' j H)
    (triangleConstantParametricNaturalitySquare a ha a' ha' v f g f' g' j H)
    (triangleFirstSecondParametricNaturalitySquare_shared a ha a' ha' v w hc f g f' g' j H)
    (triangleFirstConstantParametricNaturalitySquare_shared a ha a' ha' v w hc f g f' g' j H)

/-- 同じ実際の逆区間の前後合成の自然性。元の合成・逆三角形を選び直さない。 -/
def reverseParametricNaturalitySquare :
    SSet.Homotopy ((((reverseComposite a ha f g).path).basedPost (targetParametricPost v)).path)
      (((((reverseComposite a' ha' f' g').path).basedIhomMap P).pre j).path) := by
  let C := reverseParametricNaturalityComparison a ha a' ha' v w hc f g f' g' j H
  let S := SquareAdjustment.TrianglePairComparison.square _ _ _ _ _ _ _ C
  exact {
    h := S.h
    h₀ := S.h₀.trans (parametricPostTrianglePair_inverse_zero a ha f g v)
    h₁ := S.h₁.trans (parametricPreTrianglePair_inverse_zero a' ha' f' g' j)
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は元の第二辺の自然性正方形の終境界を保持する。 -/
lemma reverseParametricNaturalitySquare_left :
    SquareAdjustment.leftSide ≫ (reverseParametricNaturalitySquare a ha a' ha' v w hc f g f' g'
      j H).h =
      SquareAdjustment.rightSide ≫ (secondPathParametricNaturalitySquare f g f' g' j v H).h :=
  SquareAdjustment.TrianglePairComparison.left _ _ _ _ _ _ _
    (reverseParametricNaturalityComparison a ha a' ha' v w hc f g f' g' j H)

/-- 右境界全体も元の第三正方形の終境界を保持する。 -/
lemma reverseParametricNaturalitySquare_right :
    SquareAdjustment.rightSide ≫ (reverseParametricNaturalitySquare a ha a' ha' v w hc f g f'
      g' j H).h =
      SquareAdjustment.rightSide ≫ (constantPathParametricNaturalitySquare f g f' g' j v H).h :=
  SquareAdjustment.TrianglePairComparison.right _ _ _ _ _ _ _
    (reverseParametricNaturalityComparison a ha a' ha' v w hc f g f' g' j H)

end SerrePositivity.KST.Spectra.SignedAdjointPaths
