module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofFiberCoefficients
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse

/-! # 共通実 fiber の閉分母表示と実係数

概要：還元の共通実頂点を、同じ実辺を持つ厳密閉分母として表示する。
方針：既存の頂点回収を使い、始対象の定義的一致で同じ元・商の係数を保つ。
規約：新しい任意の分母を選ばない。使われ方：有限閉係数充填定理への直接入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}
variable {i : L ⟶ K} {a : L ⟶ dgRoofCorrespondence A D P x y}
variable {g : K ⟶ dgQuotientRoofCorrespondence A D P x y}
variable (R : DGActualRoofFiberReduction A D P x y i a g)

/-- 共通実分母頂点を厳密に回収した閉分母。 -/
def dgActualRoofReductionDenominator : DGClosedVerdierDenominators A D P x :=
  dgVerdierOverVertexClosed A D P x R.cone.vertex

/-- 回収した閉分母の実頂点は元の共通 apex と厳密に一致する。 -/
lemma dgActualRoofReductionDenominator_vertex :
    dgClosedVerdierDenominatorVertex A D P x (dgActualRoofReductionDenominator A D P x y R) =
      R.cone.vertex := dgVerdierOverVertexClosed_vertex A D P x R.cone.vertex

/-- 同じ元係数を回収した閉分母の始対象からの Hom として表示する。 -/
def dgActualRoofClosedSourceCoefficient : L ⟶
    DGNerve.pinchedHom A D
      (ForgetEnrichment.to (Complex A) (dgActualRoofReductionDenominator A D P x y R).obj.left) y :=
  dgActualRoofSourceCoefficient A D P x y R

/-- 同じ商係数を回収した同じ閉分母の始対象からの Hom として表示する。 -/
def dgActualRoofClosedTargetCoefficient : K ⟶
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj
        (ForgetEnrichment.to (Complex A) (dgActualRoofReductionDenominator A D P x y R).obj.left))
      ((DGQuotient.inclusion A D P).obj y) :=
  dgActualRoofTargetCoefficient A D P x y R

/-- 回収した同じ閉分母の係数上で相対正方形は厳密に可換。 -/
lemma dgActualRoofClosedCoefficient_square :
    dgActualRoofClosedSourceCoefficient A D P x y R ≫
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (Complex A)
          (dgActualRoofReductionDenominator A D P x y R).obj.left) y) =
      i ≫ dgActualRoofClosedTargetCoefficient A D P x y R :=
  dgActualRoofCoefficient_square A D P x y R

end SerrePositivity.InfinityCategories
