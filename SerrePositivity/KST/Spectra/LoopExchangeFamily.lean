module

public import SerrePositivity.KST.Spectra.TwoLoopSourceCoordinates
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies
public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus

/-!
概要：同じ内側の源に対する実交換区間と境界固定自然性を、移送用のデータに束ねる。
方針：元の区間・二次元射・左右全境界を明示し、具体的な普遍源で全て構成する。
規約：このデータの存在を仮定しない。使われ方：通常円の構成を元の随伴へ移す一般補題。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra

/-- 実際の区間・正方形・全境界を持つ、固定した内側の源の交換族。 -/
structure LoopExchangeFamily (S : PointedSimplicialSet.{u}) where
  interval : ∀ (Z : PointedSimplicialSet.{u}) [KanComplex Z.right],
    PointedMapping.VerticalPath (PointedObject.toPoint
      (LoopExchangePaths.doubleLoop (PointedObject.basedHom S Z)))
      (LoopExchangePaths.swap (PointedObject.basedHom S Z))
      (LoopExchangePaths.reversal (PointedObject.basedHom S Z))
  naturality : ∀ {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
    (v : Z ⟶ Z'), SSet.Homotopy
      (((interval Z).basedPost (TwoLoopSource.loopPost S v)).path)
      (((interval Z').pre (TwoLoopSource.loopPost S v)).path)
  start : ∀ {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
    (v : Z ⟶ Z'), SquareAdjustment.leftSide ≫ (naturality v).h =
      SSet.const (PointedMapping.familyVertex (TwoLoopSource.loopPost S v ≫
        LoopExchangePaths.swap (PointedObject.basedHom S Z')))
  finish : ∀ {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
    (v : Z ⟶ Z'), SquareAdjustment.rightSide ≫ (naturality v).h =
      SSet.const (PointedMapping.familyVertex (TwoLoopSource.loopPost S v ≫
        LoopExchangePaths.reversal (PointedObject.basedHom S Z')))

end SerrePositivity.KST.Spectra
