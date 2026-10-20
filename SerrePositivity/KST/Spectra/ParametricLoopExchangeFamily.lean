module

public import SerrePositivity.KST.Spectra.LoopExchangeFamily
public import SerrePositivity.KST.Spectra.OrdinaryLoopParametricStandardAction

/-!
概要：元の同じ交換族へ、標準作用の全族自然性と両端全境界を供給するデータ。
方針：元の族をそのまま保持し、通常円の同じ実正方形と境界の証明を全て供給する。
規約：このデータの存在を仮定しない。使われ方：元の随伴への trace の全族自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra

/-- 元の同じ区間の族と、標準反復作用の全族正方形・全境界を保持するデータ。 -/
structure ParametricLoopExchangeFamily (S : PointedSimplicialSet.{u}) where
  underlying : LoopExchangeFamily S
  naturality : ∀ {P Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right] (v : P ⟶ PointedObject.basedHom Z Z'),
    SSet.Homotopy
      (((underlying.interval Z).basedPost (TwoLoopSource.standardParametricPost S v)).path)
      ((((underlying.interval Z').basedIhomMap P).pre
        (TwoLoopSource.standardParametricPost S v)).path)
  start : ∀ {P Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right] (v : P ⟶ PointedObject.basedHom Z Z'),
    SquareAdjustment.leftSide ≫ (naturality v).h =
      SSet.const (PointedMapping.familyVertex (TwoLoopSource.standardParametricPost S v ≫
        PointedObject.basedHomMap P (LoopExchangePaths.swap (PointedObject.basedHom S Z'))))
  finish : ∀ {P Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right] (v : P ⟶ PointedObject.basedHom Z Z'),
    SquareAdjustment.rightSide ≫ (naturality v).h =
      SSet.const (PointedMapping.familyVertex (TwoLoopSource.standardParametricPost S v ≫
        PointedObject.basedHomMap P (LoopExchangePaths.reversal (PointedObject.basedHom S Z'))))

namespace OrdinaryLoopSource

/-- 現在の通常円の同じ交換族に、証明済みの標準全族自然性と全境界を供給する。 -/
def parametricFamily : ParametricLoopExchangeFamily PointedSimplicialSet.circle.{u} where
  underlying := family.{u}
  naturality v := loopExchangeStandardParametricNaturalitySquare v
  start v := loopExchangeStandardParametricNaturalitySquare_start v
  finish v := loopExchangeStandardParametricNaturalitySquare_finish v

/-- 元の交換区間・固定射の自然性・trace に使う族は、そのままの現在の族。 -/
lemma parametricFamily_underlying : parametricFamily.{u}.underlying = family.{u} := rfl

end OrdinaryLoopSource
end SerrePositivity.KST.Spectra
