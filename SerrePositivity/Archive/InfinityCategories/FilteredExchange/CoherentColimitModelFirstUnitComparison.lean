module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitModelFirstUnitValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueToReflection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：元の模型第一辺比較を同じ raw fiber に戻し、元の第一辺合成比較と値まで同定する。
方針：固定値射の充満忠実性で元の模型指定値の逆像を取り、その像を反映する。
規約：模型指定値・二実端点を保持。使われ方：最後辺への輸送を元の模型比較で表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 元の模型第一辺比較の同じ指定値を、元の raw fiber の同じ二実端点へ戻す。 -/
def coherentColimitModelFirstUnitComparison :
    FunctorIso (u₀ ≫ (P ≫ coherentColimitRawFiberTransport B a))
      (coherentColimitRawUpperCompositeAction B a ≫ PG) :=
  IsFullyFaithful.preimageFunctorIso
    (pointedFiberValueTo_isQCatEquivalence (coherentDiagramTotalCocone_vertex G)).isFullyFaithful
    (coherentColimitModelFirstUnitValueIso B a)

/-- 同じ逆像を元の固定値へ写すと、元の模型第一辺の指定値が厳密に回収される。 -/
lemma coherentColimitModelFirstUnitComparison_value :
    (coherentColimitModelFirstUnitComparison B a).postcomp V =
      coherentColimitModelFirstUnitValueIso B a := by
  exact IsFullyFaithful.preimageFunctorIso_postcomp _ _

/-- 元の模型第一辺比較の逆像は、元の逆第一辺・二面合成比較そのもの。 -/
lemma coherentColimitModelFirstUnitComparison_eq_raw :
    coherentColimitModelFirstUnitComparison B a = coherentColimitRawFirstUnitComparison B a := by
  apply pointedFiberValueTo_postcompose_functorIso_injective (leftUnstraightening F)
    (coherentDiagramTotalCocone_vertex G)
  exact (coherentColimitModelFirstUnitComparison_value B a).trans
    (coherentColimitModelFirstUnitValueIso_eq_raw B a)

end SerrePositivity.InfinityCategories.F2
