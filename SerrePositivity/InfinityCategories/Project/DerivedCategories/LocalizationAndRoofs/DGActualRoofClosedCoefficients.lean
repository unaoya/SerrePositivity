module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofFiberCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverVertexInverse

/-! # 共通実 fiber の閉分母表示と実係数

概要：還元の共通実頂点を、同じ実辺を持つ厳密閉分母として表示する。
方針：既存の頂点回収を使い、始対象の定義的一致で同じ元・商の係数を保つ。
規約：新しい任意の分母を選ばない。使われ方：有限閉係数充填定理への直接入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}
variable {i : L ⟶ K} {a : L ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofFiberReduction A D P x y i a g)

/-- 共通実分母頂点を厳密に回収した閉分母。 -/
def dgActualRoofReductionDenominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertexClosed A D P x R.cone.vertex

/-- 回収した閉分母の実頂点は元の共通 apex と厳密に一致する。 -/
lemma dgActualRoofReductionDenominator_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x (dgActualRoofReductionDenominator A D P x y R) =
      R.cone.vertex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertexClosed_vertex A D P x R.cone.vertex

/-- 同じ元係数を回収した閉分母の始対象からの Hom として表示する。 -/
def dgActualRoofClosedSourceCoefficient : L ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgActualRoofReductionDenominator A D P x y R).obj.left) y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSourceCoefficient A D P x y R

/-- 同じ商係数を回収した同じ閉分母の始対象からの Hom として表示する。 -/
def dgActualRoofClosedTargetCoefficient : K ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgActualRoofReductionDenominator A D P x y R).obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofTargetCoefficient A D P x y R

/-- 回収した同じ閉分母の係数上で相対正方形は厳密に可換。 -/
lemma dgActualRoofClosedCoefficient_square :
    dgActualRoofClosedSourceCoefficient A D P x y R ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
          (dgActualRoofReductionDenominator A D P x y R).obj.left) y) =
      i ≫ dgActualRoofClosedTargetCoefficient A D P x y R :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofCoefficient_square A D P x y R

end SerrePositivity.InfinityCategories.Project.DerivedCategories
