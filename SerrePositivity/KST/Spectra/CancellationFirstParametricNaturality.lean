module

public import SerrePositivity.KST.Spectra.OrdinaryParametricExchangeNaturality
public import SerrePositivity.KST.Spectra.CancellationFirstNaturality

/-!
概要：元の交換符号区間の全族自然性から、同じ第一辺の全族正方形を構成する。
方針：元の自然性正方形の二次元射へ反転を作用させ、厳密可換式で全辺を照合する。
規約：同じ実区間・正方形を保持する。使われ方：指定合成・逆向き三角形の高次比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra
namespace LoopExchangePaths

variable {P Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Y'.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Y' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : P ⟶ PointedObject.basedHom Y Y')
  (w : P ⟶ PointedObject.basedHom Z Z')
  (hc : a ≫ PointedMapping.parametricPost PointedSimplicialSet.circle.{u} w =
    PointedMapping.transpose v ≫ PointedObject.basedHomMap P a')

/-- 元の第一辺の前後合成を、同じ交換自然性の二次元射から結ぶ実正方形。 -/
def cancellationFirstParametricNaturalitySquare :
    SSet.Homotopy (((cancellationFirst a ha).basedPost (doubleParametricPost v)).path)
      ((((cancellationFirst a' ha').basedIhomMap P).pre (doubleParametricPost v)).path) where
  h := (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h ≫
    (PointedObject.basedHomMap (doubleLoop Y) (PointedObject.basedHomMap P (reversal Y'))).right
  h₀ := by
    rw [← Category.assoc, (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h₀]
    exact ((exchange a ha).basedPost_square_path (reversal Y) (doubleParametricPost v)
      (PointedObject.basedHomMap P (reversal Y')) (reversal_doubleParametricPost v)).symm
  h₁ := by
    rw [← Category.assoc, (ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h₁]
    exact (((exchange a' ha').basedIhomMap P).pre_basedPost_path
      (doubleParametricPost v) (PointedObject.basedHomMap P (reversal Y'))).symm.trans
      (congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doubleParametricPost v) _).right)
        ((exchange a' ha').basedIhomMap_post_path P (reversal Y')).symm)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 第一辺の自然性正方形の左辺全体は、同じ交換・反転の合成頂点で一定。 -/
lemma cancellationFirstParametricNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (cancellationFirstParametricNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex ((swap Y ≫ reversal Y) ≫ doubleParametricPost v))
        := by
  change SquareAdjustment.leftSide ≫
    ((ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h ≫ _) = _
  rw [← Category.assoc, ordinaryParametricExchangeNaturalitySquare_start, SSet.const_comp,
    PointedMapping.familyVertex_post]
  have he : (swap Y ≫ doubleParametricPost v) ≫ PointedObject.basedHomMap P (reversal Y') =
    (swap Y ≫ reversal Y) ≫ doubleParametricPost v := by
    rw [Category.assoc, ← reversal_doubleParametricPost v, ← Category.assoc]
  exact congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he

/-- 右辺全体も、同じ二重反転の合成頂点で一定。 -/
lemma cancellationFirstParametricNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (cancellationFirstParametricNaturalitySquare a ha a' ha' v w
      hc).h =
      SSet.const (PointedMapping.familyVertex ((reversal Y ≫ reversal Y) ≫ doubleParametricPost
        v)) := by
  change SquareAdjustment.rightSide ≫
    ((ordinaryParametricExchangeNaturalitySquare a ha a' ha' v w hc).h ≫ _) = _
  rw [← Category.assoc, ordinaryParametricExchangeNaturalitySquare_finish, SSet.const_comp,
    PointedMapping.familyVertex_post]
  have he : (reversal Y ≫ doubleParametricPost v) ≫ PointedObject.basedHomMap P (reversal Y') =
      (reversal Y ≫ reversal Y) ≫ doubleParametricPost v := by
    rw [Category.assoc, ← reversal_doubleParametricPost v, ← Category.assoc]
  exact congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he

end LoopExchangePaths
end SerrePositivity.KST.Spectra
