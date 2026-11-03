module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstUnitEndpoints

/-!
概要：逆第一辺指定比較と同じ raw 二面比較を、元の実中間点で合成する。
方針：元の単位で前合成し、実中間射の結合だけを揃える。
規約：二つの元の指定比較を保持。使われ方：長辺残余の第一因子と二面輸送の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))

/-- 元の逆第一辺指定比較を、二面比較の同じ実始点まで保持する。 -/
def coherentColimitRawFirstUnitInversePoint :
    FunctorIso (u₀ ≫ (P ≫ coherentColimitRawFiberTransport B a))
      (coherentColimitRawLowerCompositeAction B a ≫ PG) :=
  functorIsoOfEq ((coherentColimitConstantTransportRawPointIso B a).precomp u₀).symm rfl
    (coherentColimitRawFirstUnit_middle_map B a)

/-- 元の逆第一辺指定比較と元の二面比較の、同じ raw fiber 上の合成。 -/
def coherentColimitRawFirstUnitComparison :
    FunctorIso (u₀ ≫ (P ≫ coherentColimitRawFiberTransport B a))
      (coherentColimitRawUpperCompositeAction B a ≫ PG) :=
  coherentColimitRawFirstUnitInversePoint B a ≪≫ coherentColimitRawUnitFiberComparison B a

end SerrePositivity.InfinityCategories.F2
