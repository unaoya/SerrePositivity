module

public import SerrePositivity.KST.Spectra.DeloopedExchangePostPasting
public import SerrePositivity.KST.Spectra.DeloopedExchangePreSquare
public import SerrePositivity.KST.Spectra.DeloopedExchangeSquareCoordinates

/-!
概要：二つの Ω 条件の可換式を使い、源側の射影比較を同じ普遍区間へ照合する。
方針：二重後合成の厳密可換式で終辺を合わせ、元の作用の自然性で左右境界も合わせる。
規約：実正方形を選び直さない。使われ方：共通終辺の相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

variable {Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y'.right]
  [KanComplex Z'.right]
  (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (h' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (hh' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h'.right) (v : Y ⟶ Y') (w : Z ⟶ Z')
  (hc : h ≫ PointedObject.basedHomMap CirclePower.space.{u} w = v ≫ h')

include hc

/-- 同じ源前合成の正方形を、標的後合成側と厳密に同じ普遍終辺へ表示する。 -/
def exchangeAlignedPreSquare :
    SSet.Homotopy
      ((((deloopedExchange h' hh').basedPost (doublePost h')).pre (doublePost v)).path)
      (((TripleCircle.loopExchangeInterval Z').pre
        (doublePost h ≫ TripleCircle.loopPost w)).path) where
  h := (exchangePreProjectionSquare h' hh' (doublePost v)).h
  h₀ := (exchangePreProjectionSquare h' hh' (doublePost v)).h₀
  h₁ := by
    rw [(exchangePreProjectionSquare h' hh' (doublePost v)).h₁]
    change (TripleCircle.loopExchangeInterval Z').path ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost v ≫ doublePost h') _).right =
      (TripleCircle.loopExchangeInterval Z').path ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doublePost h ≫ TripleCircle.loopPost w) _).right
    rw [doublePost_square h h' v w hc]
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Y'.right] [KanComplex Z'.right] in
/-- 始点作用の元の入力像は、標的後合成側と同じ厳密な射。 -/
lemma exchangeNaturality_swap_vertex :
    doublePost v ≫ (swap Y' ≫ doublePost h') =
      (swap Y ≫ doublePost h) ≫ TripleCircle.loopPost w := by
  rw [← Category.assoc, ← swap_doublePost v, Category.assoc,
    ← doublePost_square h h' v w hc, ← Category.assoc]

omit [KanComplex Y'.right] [KanComplex Z'.right] in
/-- 終点作用の元の入力像も、標的後合成側と同じ厳密な射。 -/
lemma exchangeNaturality_reversal_vertex :
    doublePost v ≫ (reversal Y' ≫ doublePost h') =
      (reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost w := by
  rw [← Category.assoc, ← reversal_doublePost v, Category.assoc,
    ← doublePost_square h h' v w hc, ← Category.assoc]

/-- 同じ普遍終辺へそろえた正方形の左辺も、元の交換作用の同じ像で一定。 -/
lemma exchangeAlignedPreSquare_start :
    SquareAdjustment.leftSide ≫ (exchangeAlignedPreSquare h h' hh' v w hc).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TripleCircle.loopPost w)) := by
  change SquareAdjustment.leftSide ≫
    (exchangePreProjectionSquare h' hh' (doublePost v)).h = _
  rw [exchangePreProjectionSquare_start, exchangeNaturality_swap_vertex h h' v w hc]

/-- 右辺全体も、元の反転作用の同じ像で一定。 -/
lemma exchangeAlignedPreSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeAlignedPreSquare h h' hh' v w hc).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost w)) := by
  change SquareAdjustment.rightSide ≫
    (exchangePreProjectionSquare h' hh' (doublePost v)).h = _
  rw [exchangePreProjectionSquare_finish, exchangeNaturality_reversal_vertex h h' v w hc]

end SerrePositivity.KST.Spectra.LoopExchangePaths
