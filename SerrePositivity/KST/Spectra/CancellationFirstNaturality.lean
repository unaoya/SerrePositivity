module

public import SerrePositivity.KST.Spectra.OrdinaryExchangeNaturality

/-!
概要：元の交換符号区間へ同じ反転を後合成し、単位構造の第一辺の自然性を構成する。
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
namespace PointedMapping.VerticalPath

/-- 厳密な可換式は、元の同じ区間への二つの後合成を辺全体で照合する。 -/
lemma basedPost_square_path {A E E' : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (P : VerticalPath (PointedObject.toPoint E) f g) (r : E ⟶ E) (v : E ⟶ E')
    (r' : E' ⟶ E') (hc : r ≫ v = v ≫ r') :
    ((P.basedPost r).basedPost v).path = ((P.basedPost v).basedPost r').path := by
  rw [basedPost_basedPost_path, basedPost_basedPost_path, hc]

end PointedMapping.VerticalPath
namespace LoopExchangePaths

variable {Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Y'.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (a' : Y' ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right) (v : Y ⟶ Y') (w : Z ⟶ Z')
  (hc : a ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} w = v ≫ a')

/-- 元の第一辺の前後合成を、同じ交換自然性の二次元射から結ぶ実正方形。 -/
def cancellationFirstNaturalitySquare :
    SSet.Homotopy (((cancellationFirst a ha).basedPost (doublePost v)).path)
      (((cancellationFirst a' ha').pre (doublePost v)).path) where
  h := (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h ≫
    (PointedObject.basedHomMap (doubleLoop Y) (reversal Y')).right
  h₀ := by
    rw [← Category.assoc, (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h₀]
    exact ((exchange a ha).basedPost_square_path (reversal Y) (doublePost v)
      (reversal Y') (reversal_doublePost v)).symm
  h₁ := by
    rw [← Category.assoc, (ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h₁]
    exact ((exchange a' ha').pre_basedPost_path (doublePost v) (reversal Y')).symm
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 第一辺の自然性正方形の左辺全体は、同じ交換・反転の合成頂点で一定。 -/
lemma cancellationFirstNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (cancellationFirstNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex ((swap Y ≫ reversal Y) ≫ doublePost v)) := by
  change SquareAdjustment.leftSide ≫
    ((ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h ≫ _) = _
  rw [← Category.assoc, ordinaryExchangeNaturalitySquare_start, SSet.const_comp,
    PointedMapping.familyVertex_post]
  have he : (swap Y ≫ doublePost v) ≫ reversal Y' = (swap Y ≫ reversal Y) ≫ doublePost v := by
    rw [Category.assoc, ← reversal_doublePost v, ← Category.assoc]
  exact congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he

/-- 右辺全体も、同じ二重反転の合成頂点で一定。 -/
lemma cancellationFirstNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (cancellationFirstNaturalitySquare a ha a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex ((reversal Y ≫ reversal Y) ≫ doublePost v)) := by
  change SquareAdjustment.rightSide ≫
    ((ordinaryExchangeNaturalitySquare a ha a' ha' v w hc).h ≫ _) = _
  rw [← Category.assoc, ordinaryExchangeNaturalitySquare_finish, SSet.const_comp,
    PointedMapping.familyVertex_post]
  have he : (reversal Y ≫ doublePost v) ≫ reversal Y' =
      (reversal Y ≫ reversal Y) ≫ doublePost v := by
    rw [Category.assoc, ← reversal_doublePost v, ← Category.assoc]
  exact congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he

end LoopExchangePaths
end SerrePositivity.KST.Spectra
