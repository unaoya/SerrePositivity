module

public import SerrePositivity.KST.Spectra.DeloopedExchangeProjectionSquare

/-!
概要：別の Ω 条件の同じ射影比較正方形へ源前合成し、普遍交換区間の制限へ戻す。
方針：二次元射に同じ内部 Hom の源制限を作用させ、合成入力の実辺を照合する。
規約：新しい辺や充填を選ばない。使われ方：交換自然性の共通終辺の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

variable {A Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
  (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) (a : A ⟶ doubleLoop Y)

/-- 同じ射影比較を源へ前合成し、元の普遍区間の同じ合成入力へ至る実正方形。 -/
def exchangePreProjectionSquare :
    SSet.Homotopy
      ((((deloopedExchange h hh).basedPost (doublePost h)).pre a).path)
      (((TripleCircle.loopExchangeInterval Z).pre (a ≫ doublePost h)).path) where
  h := (exchangeProjectionSquare h hh).h ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a
      (doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z))).right
  h₀ := by rw [← Category.assoc, (exchangeProjectionSquare h hh).h₀]; rfl
  h₁ := by
    rw [← Category.assoc, (exchangeProjectionSquare h hh).h₁]
    exact (TripleCircle.loopExchangeInterval Z).pre_pre_path (doublePost h) a
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 源前合成した比較の左辺全体は、元の交換作用の同じ入力像で一定。 -/
lemma exchangePreProjectionSquare_start :
    SquareAdjustment.leftSide ≫ (exchangePreProjectionSquare h hh a).h =
      SSet.const (PointedMapping.familyVertex (a ≫ (swap Y ≫ doublePost h))) := by
  change SquareAdjustment.leftSide ≫ ((exchangeProjectionSquare h hh).h ≫ _) = _
  rw [← Category.assoc, exchangeProjectionSquare_start, SSet.const_comp]
  congr 1
  exact PointedMapping.familyVertex_pre a (swap Y ≫ doublePost h)

/-- 源前合成した比較の右辺全体も、元の反転作用の同じ入力像で一定。 -/
lemma exchangePreProjectionSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangePreProjectionSquare h hh a).h =
      SSet.const (PointedMapping.familyVertex (a ≫ (reversal Y ≫ doublePost h))) := by
  change SquareAdjustment.rightSide ≫ ((exchangeProjectionSquare h hh).h ≫ _) = _
  rw [← Category.assoc, exchangeProjectionSquare_finish, SSet.const_comp]
  congr 1
  exact PointedMapping.familyVertex_pre a (reversal Y ≫ doublePost h)

end SerrePositivity.KST.Spectra.LoopExchangePaths
