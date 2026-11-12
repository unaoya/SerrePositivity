module

public import SerrePositivity.KST.Spectra.DeloopedExchangePostSquares
public import SerrePositivity.KST.Spectra.ConstantBoundarySquarePasting

/-!
概要：元の交換トレースの後合成と普遍自然性の入力制限を、同じ一定境界で貼る。
方針：厳密に共有する実辺を使い、両端の定数二単体を指定して相対合成する。
規約：入力した二つの正方形と合成三角形を保持する。使われ方：一般の Ω 条件の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

variable {Y Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) (v : Z ⟶ Z')

/-- 同じ左右の定数二単体を保持した、元の二つの正方形の実際の合成データ。 -/
def exchangePostPasting :
    SquareAdjustment.ConstantBoundaryPasting
      (exchangePostProjectionSquare h hh v) (exchangeRestrictedNaturalitySquare h v)
      (PointedMapping.familyVertex ((swap Y ≫ doublePost h) ≫ TripleCircle.loopPost v))
      (PointedMapping.familyVertex ((reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) := by
  let targetKan : KanComplex (PointedObject.basedHom (doubleLoop Y)
      (doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z'))).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact SquareAdjustment.ConstantBoundaryPasting.choose _ _ _ _
    (exchangePostProjectionSquare_start h hh v) (exchangePostProjectionSquare_finish h hh v)
    (exchangeRestrictedNaturalitySquare_start h v) (exchangeRestrictedNaturalitySquare_finish h v)

/-- 元の交換区間の後合成像を、元の普遍交換区間の同じ制限へ結ぶ実正方形。 -/
def exchangePostComparisonSquare :
    SSet.Homotopy
      ((((deloopedExchange h hh).basedPost (doublePost h)).basedPost
        (TripleCircle.loopPost v)).path)
      (((TripleCircle.loopExchangeInterval Z').pre
        (doublePost h ≫ TripleCircle.loopPost v)).path) := (exchangePostPasting h hh v).homotopy

/-- 貼り合わせた正方形の左辺全体は、元の交換作用の同じ像で一定。 -/
lemma exchangePostComparisonSquare_start :
    SquareAdjustment.leftSide ≫ (exchangePostComparisonSquare h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) :=
  SquareAdjustment.ConstantBoundaryPasting.start _ _ _ _ (exchangePostPasting h hh v)

/-- 貼り合わせた正方形の右辺全体も、元の反転作用の同じ像で一定。 -/
lemma exchangePostComparisonSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangePostComparisonSquare h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TripleCircle.loopPost v)) :=
  SquareAdjustment.ConstantBoundaryPasting.finish _ _ _ _ (exchangePostPasting h hh v)

end SerrePositivity.KST.Spectra.LoopExchangePaths
