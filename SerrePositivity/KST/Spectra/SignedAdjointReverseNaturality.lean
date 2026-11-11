module

public import SerrePositivity.KST.Spectra.SignedAdjointTriangleNaturalityEdges

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
  (j : A ⟶ A') {p : LoopExchangePaths.doubleLoop Z' ⟶ B}
  (H : PointedMapping.VerticalPath p
    (input f g ≫ LoopExchangePaths.doublePost v) (j ≫ input f' g'))

local instance reverseNaturalityInnerKan :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance reverseNaturalityTargetKan : KanComplex (target Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance reverseNaturalityHomKan : KanComplex (PointedObject.basedHom A (target Z')).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の三自然性正方形と保存済み四つの実三角形を保持する、二段の相対ホーン比較。 -/
def reverseNaturalityComparison :=
  SquareAdjustment.TrianglePairComparison.choose
    (postTrianglePair a ha f g v) (preTrianglePair a' ha' f' g' j)
    (triangleFirstNaturalitySquare a ha a' ha' v w hc f g f' g' j H)
    (triangleSecondNaturalitySquare a ha a' ha' v f g f' g' j H)
    (triangleConstantNaturalitySquare a ha a' ha' v f g f' g' j H)
    (triangleFirstSecondNaturalitySquare_shared a ha a' ha' v w hc f g f' g' j H)
    (triangleFirstConstantNaturalitySquare_shared a ha a' ha' v w hc f g f' g' j H)

/-- 同じ実際の逆区間の前後合成の自然性。元の合成・逆三角形を選び直さない。 -/
def reverseNaturalitySquare :
    SSet.Homotopy ((((reverseComposite a ha f g).path).basedPost (targetPost v)).path)
      ((((reverseComposite a' ha' f' g').path).pre j).path) := by
  let C := reverseNaturalityComparison a ha a' ha' v w hc f g f' g' j H
  let S := SquareAdjustment.TrianglePairComparison.square _ _ _ _ _ _ _ C
  exact {
    h := S.h
    h₀ := S.h₀.trans (postTrianglePair_inverse_zero a ha f g v)
    h₁ := S.h₁.trans (preTrianglePair_inverse_zero a' ha' f' g' j)
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 左境界全体は元の第二辺の自然性正方形の終境界を保持する。 -/
lemma reverseNaturalitySquare_left :
    SquareAdjustment.leftSide ≫ (reverseNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.rightSide ≫ (secondPathNaturalitySquare f g f' g' j v H).h :=
  SquareAdjustment.TrianglePairComparison.left _ _ _ _ _ _ _
    (reverseNaturalityComparison a ha a' ha' v w hc f g f' g' j H)

/-- 右境界全体も元の第三正方形の終境界を保持する。 -/
lemma reverseNaturalitySquare_right :
    SquareAdjustment.rightSide ≫ (reverseNaturalitySquare a ha a' ha' v w hc f g f' g' j H).h =
      SquareAdjustment.rightSide ≫ (constantPathNaturalitySquare f g f' g' j v H).h :=
  SquareAdjustment.TrianglePairComparison.right _ _ _ _ _ _ _
    (reverseNaturalityComparison a ha a' ha' v w hc f g f' g' j H)

end SerrePositivity.KST.Spectra.SignedAdjointPaths
