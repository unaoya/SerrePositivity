module

public import SerrePositivity.KST.Spectra.DeloopedTracedExchange
public import SerrePositivity.KST.Spectra.PointedTracedPathSquare

/-!
概要：Ω 対象へ移した交換区間の実際の像を、元の普遍区間へ実正方形で比較する。
方針：同じ写像 path トレースを通常の二変数射へ評価する。
規約：両端の境界全体を固定する。使われ方：普遍交換の自然性との指定境界付き貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

variable {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
  (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right)

/-- 元の Ω 対象の交換区間の像と、同じ普遍交換区間を結ぶ実正方形。 -/
def exchangeProjectionSquare :
    SSet.Homotopy (((deloopedExchange h hh).basedPost (doublePost h)).path)
      (((TripleCircle.loopExchangeInterval Z).pre (doublePost h)).path) :=
  (exchangeTrace h hh).traceSquare

/-- 比較正方形の左辺全体は、元の交換作用の同じ像で一定。 -/
lemma exchangeProjectionSquare_start :
    SquareAdjustment.leftSide ≫ (exchangeProjectionSquare h hh).h =
      SSet.const (PointedMapping.familyVertex (swap Y ≫ doublePost h)) :=
  (exchangeTrace h hh).traceSquare_start

/-- 比較正方形の右辺全体も、元の反転作用の同じ像で一定。 -/
lemma exchangeProjectionSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangeProjectionSquare h hh).h =
      SSet.const (PointedMapping.familyVertex (reversal Y ≫ doublePost h)) :=
  (exchangeTrace h hh).traceSquare_finish

/-- 二次元射全体は、選択済みの同じ自由 path トレースの評価そのもの。 -/
lemma exchangeProjectionSquare_h :
    (exchangeProjectionSquare h hh).h =
      FreePathEvaluation.square (exchangeTrace h hh).tracePath := rfl

end SerrePositivity.KST.Spectra.LoopExchangePaths
