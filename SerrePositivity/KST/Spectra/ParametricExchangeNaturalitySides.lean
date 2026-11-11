module

public import SerrePositivity.KST.Spectra.ParametricExchangePostPasting
public import SerrePositivity.KST.Spectra.ParametricExchangePreSquare

/-!
概要：全族 Ω 可換式で、元の二つの射影比較の終辺と左右の境界をそろえる。
方針：標準の二重 loop 族作用の厳密可換式と交換・反転の自然性を使う。
規約：元の実正方形を保持する。使われ方：共通終辺での相対差と反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
open LoopExchangePaths
variable {S : PointedSimplicialSet.{u}} (I : ParametricLoopExchangeFamily S)
variable {P Y Y' Z Z' : PointedSimplicialSet.{u}} [KanComplex Y'.right]
  [KanComplex Z'.right]
  (a : Y ⟶ PointedObject.basedHom S Z) (a' : Y' ⟶ PointedObject.basedHom S Z')
  (ha' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a'.right)
  (v : P ⟶ PointedObject.basedHom Y Y') (w : P ⟶ PointedObject.basedHom Z Z')
  (hc : a ≫ PointedMapping.parametricPost S w =
    PointedMapping.transpose v ≫ PointedObject.basedHomMap P a')
include hc

/-- 同じ全族源制限の射影比較を、後合成側と同じ普遍終辺へ表示する。 -/
def exchangeAlignedPreSquare :=
  exchangePreProjectionSquareTo I a' ha' (doubleParametricPost v)
    (doublePost a ≫ TwoLoopSource.standardParametricPost S w)
    (doublePost_parametric_square a a' v w hc).symm

omit [KanComplex Y'.right] [KanComplex Z'.right] in
/-- 元の交換作用の全族入力像は、標的側と同じ厳密な射。 -/
lemma exchangeNaturality_swap_vertex :
    doubleParametricPost v ≫ PointedObject.basedHomMap P (swap Y' ≫ doublePost a') =
      (swap Y ≫ doublePost a) ≫ TwoLoopSource.standardParametricPost S w := by
  have hm : PointedObject.basedHomMap P (swap Y' ≫ doublePost a') =
      PointedObject.basedHomMap P (swap Y') ≫
        PointedObject.basedHomMap P (doublePost a') :=
    CategoryTheory.Functor.map_comp (ihom P) _ _
  rw [hm, ← Category.assoc, ← swap_doubleParametricPost,
    Category.assoc, ← doublePost_parametric_square a a' v w hc, ← Category.assoc]

omit [KanComplex Y'.right] [KanComplex Z'.right] in
/-- 元の反転作用の全族入力像も、標的側と同じ厳密な射。 -/
lemma exchangeNaturality_reversal_vertex :
    doubleParametricPost v ≫ PointedObject.basedHomMap P (reversal Y' ≫ doublePost a') =
      (reversal Y ≫ doublePost a) ≫ TwoLoopSource.standardParametricPost S w := by
  have hm : PointedObject.basedHomMap P (reversal Y' ≫ doublePost a') =
      PointedObject.basedHomMap P (reversal Y') ≫
        PointedObject.basedHomMap P (doublePost a') :=
    CategoryTheory.Functor.map_comp (ihom P) _ _
  rw [hm, ← Category.assoc, ← reversal_doubleParametricPost,
    Category.assoc, ← doublePost_parametric_square a a' v w hc, ← Category.assoc]

/-- 同じ普遍終辺へそろえた正方形の左辺も、同じ交換像で一定。 -/
lemma exchangeAlignedPreSquare_start :
    SquareAdjustment.leftSide ≫ (exchangeAlignedPreSquare I a a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost a) ≫ TwoLoopSource.standardParametricPost S w)) := by
  change SquareAdjustment.leftSide ≫
    (exchangePreProjectionSquare I a' ha' (doubleParametricPost v)).h = _
  rw [exchangePreProjectionSquare_start I, exchangeNaturality_swap_vertex a a' v w hc]

/-- 同じ右辺全体も、同じ反転像で一定。 -/
lemma exchangeAlignedPreSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeAlignedPreSquare I a a' ha' v w hc).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost a) ≫ TwoLoopSource.standardParametricPost S w)) := by
  change SquareAdjustment.rightSide ≫
    (exchangePreProjectionSquare I a' ha' (doubleParametricPost v)).h = _
  rw [exchangePreProjectionSquare_finish I, exchangeNaturality_reversal_vertex a a' v w hc]

end SerrePositivity.KST.Spectra.ParametricLoopExchangeFamily
