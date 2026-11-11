module

public import SerrePositivity.KST.Spectra.SignedAdjointNaturalityCoordinates
public import SerrePositivity.KST.Spectra.PointedIntervalProjectedSquare

/-!
概要：元の交換符号辺の移送自然性に同じ入力と射影を付け、実際の第一辺へ照合する。
方針：現在の同じ交換区間の自然性正方形へ、内部 Hom の前後合成を作用させる。
規約：第一辺の実区間と全境界を保持。使われ方：後続の実入力正方形との貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths
variable {A Y Z Z' W W' : PointedSimplicialSet.{u}}
  [KanComplex Z.right] [KanComplex Z'.right] [KanComplex W.right] [KanComplex W'.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Z' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : Z ⟶ Z') (w : W ⟶ W')
  (hc : a ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} w = v ≫ a')
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)

/-- 同じ元の第一辺の後合成から、移した入力での同じ標的交換区間へ至る実正方形。 -/
def firstPathPostNaturalitySquare :
    SSet.Homotopy (((firstPath a ha f g).basedPost (targetPost v)).path)
      ((((cancellationFirst a' ha').basedPost (projection Z')).pre
        (input f g ≫ doublePost v)).path) := by
  let S := PointedMapping.VerticalPath.projectedNaturalitySquare
    (cancellationFirst a ha) (cancellationFirst a' ha') (input f g) (doublePost v)
    (projection Z) (projection Z') (targetPost v) (projection_natural v)
    (cancellationFirstNaturalitySquare a ha a' ha' v w hc)
  exact {
    h := S.h
    h₀ := S.h₀
    h₁ := S.h₁.trans ((cancellationFirst a' ha').pre_basedPost_path
      (input f g ≫ doublePost v) (projection Z')).symm
    rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim }

/-- 移送自然性の左境界全体は、元の同じ交換・反転頂点の指定像で一定。 -/
lemma firstPathPostNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (firstPathPostNaturalitySquare a ha a' ha' v w hc f g).h =
      SSet.const (((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (doubleLoop Z')).right ≫
        (PointedObject.basedHomMap A (projection Z')).right).app _
          (PointedMapping.familyVertex ((swap Z ≫ reversal Z) ≫ doublePost v))) := by
  change SquareAdjustment.leftSide ≫
    ((cancellationFirstNaturalitySquare a ha a' ha' v w hc).h ≫ _) = _
  rw [← Category.assoc, cancellationFirstNaturalitySquare_start, SSet.const_comp]

/-- 移送自然性の右境界全体も、元の同じ二重反転頂点の指定像で一定。 -/
lemma firstPathPostNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (firstPathPostNaturalitySquare a ha a' ha' v w hc f g).h =
      SSet.const (((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (input f g) (doubleLoop Z')).right ≫
        (PointedObject.basedHomMap A (projection Z')).right).app _
          (PointedMapping.familyVertex ((reversal Z ≫ reversal Z) ≫ doublePost v))) := by
  change SquareAdjustment.rightSide ≫
    ((cancellationFirstNaturalitySquare a ha a' ha' v w hc).h ≫ _) = _
  rw [← Category.assoc, cancellationFirstNaturalitySquare_finish, SSet.const_comp]

end SerrePositivity.KST.Spectra.SignedAdjointPaths
