module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportRawPoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerPointValueToEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUnitFiberModel

/-!
概要：逆第一辺比較と raw 二面比較を繋ぐ三つの実端点を計算する。
方針：元の単位作用・指定一点終点・値射の公式を使う。
規約：端点を実射から回収する。使われ方：二比較の合成と元の模型単位比較への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (coconeTransformationVertex (coherentDiagramTotalCocone F)))
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy ca))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 逆第一辺比較の終点は、raw 二面比較の同じ元の実始点。 -/
lemma coherentColimitRawFirstUnit_middle_map :
    u₀ ≫ (ma ≫ PG) = coherentColimitRawLowerCompositeAction B a ≫ PG := by
  unfold coherentColimitRawLowerCompositeAction
  rw [coherentVertexOfHomotopy_cocone]
  simp only [Category.assoc]

/-- 逆第一辺比較の実始点の値は、元の模型単位比較の同じ始点。 -/
lemma coherentColimitRawFirstUnit_source_value_vertex :
    functorVertex ((u₀ ≫ (P ≫ coherentColimitRawFiberTransport B a)) ≫ V) =
      functorVertex (coconeFiberMap (coherentDiagramTotalCocone F) ≫
        coherentColimitFiberTransport B a ≫
          (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) := by
  rw [← coherentColimitConstantTransport_raw_point_target B a]
  exact coherentColimitLowerPoint_target_valueTo_vertex B a

/-- 元の逆第一辺比較の実終点の値は、同じ元の下面合成作用。 -/
lemma coherentColimitRawFirstUnit_middle_value_vertex :
    functorVertex ((u₀ ≫ (ma ≫ PG)) ≫ V) =
      functorVertex (coherentColimitLowerCompositeAction B a) := by
  rw [coherentColimitRawFirstUnit_middle_map, coherentColimitRawUnitFiberValue_source_map]

/-- 元の下側因子は、同じ raw 第一辺指定比較を元の単位・値で写した指定値。 -/
lemma coherentColimitLowerTransportFactorIso_heq_raw_point :
    HEq (coherentColimitLowerTransportFactorIso B a)
      (((coherentColimitConstantTransportRawPointIso B a).precomp u₀).postcomp V) := by
  exact (coherentColimitLowerTransportFactorIso_heq_constant_point_valueTo B a).trans
    (functorIsoOfEq_precomp_postcomp_heq (coherentColimitConstantTransportPointIso B a) rfl
      (coherentColimitConstantTransport_raw_point_target B a) u₀ V).symm

end SerrePositivity.InfinityCategories.F2
