module

public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.LoopExchangeFamilyPostSquares
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
namespace SerrePositivity.KST.Spectra.LoopExchangeFamily
open LoopExchangePaths
variable {S : PointedSimplicialSet.{u}} (I : LoopExchangeFamily S)

variable {Y Z Z' : PointedSimplicialSet.{u}} [KanComplex Y.right]
  [KanComplex Z.right] [KanComplex Z'.right]
  (h : Y ⟶ PointedObject.basedHom S Z)
  (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) (v : Z ⟶ Z')

/-- 同じ左右の定数二単体を保持した、元の二つの正方形の実際の合成データ。 -/
def exchangePostPasting :
    SquareAdjustment.ConstantBoundaryPasting
      (exchangePostProjectionSquare I h hh v) (exchangeRestrictedNaturalitySquare I h v)
      (PointedMapping.familyVertex ((swap Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S v))
      (PointedMapping.familyVertex ((reversal Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S v)) := by
  let targetKan : KanComplex (PointedObject.basedHom (doubleLoop Y)
      (doubleLoop (PointedObject.basedHom S Z'))).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact SquareAdjustment.ConstantBoundaryPasting.choose _ _ _ _
    (exchangePostProjectionSquare_start I h hh v) (exchangePostProjectionSquare_finish I h hh v)
    (exchangeRestrictedNaturalitySquare_start I h v)
    (exchangeRestrictedNaturalitySquare_finish I h v)

/-- 元の交換区間の後合成像を、元の普遍交換区間の同じ制限へ結ぶ実正方形。 -/
def exchangePostComparisonSquare :
    SSet.Homotopy
      ((((exchange I h hh).basedPost (doublePost h)).basedPost
        (TwoLoopSource.loopPost S v)).path)
      (((I.interval Z').pre
        (doublePost h ≫ TwoLoopSource.loopPost S v)).path) :=
  (exchangePostPasting I h hh v).homotopy

/-- 貼り合わせた正方形の左辺全体は、元の交換作用の同じ像で一定。 -/
lemma exchangePostComparisonSquare_start :
    SquareAdjustment.leftSide ≫ (exchangePostComparisonSquare I h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((swap Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S v)) :=
  SquareAdjustment.ConstantBoundaryPasting.start _ _ _ _ (exchangePostPasting I h hh v)

/-- 貼り合わせた正方形の右辺全体も、元の反転作用の同じ像で一定。 -/
lemma exchangePostComparisonSquare_finish :
    SquareAdjustment.rightSide ≫ (exchangePostComparisonSquare I h hh v).h =
      SSet.const (PointedMapping.familyVertex
        ((reversal Y ≫ doublePost h) ≫ TwoLoopSource.loopPost S v)) :=
  SquareAdjustment.ConstantBoundaryPasting.finish _ _ _ _ (exchangePostPasting I h hh v)

end SerrePositivity.KST.Spectra.LoopExchangeFamily
