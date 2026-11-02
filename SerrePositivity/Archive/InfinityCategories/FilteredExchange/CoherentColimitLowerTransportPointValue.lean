module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerTransportRawComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoconeIntervalHomUnitValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPrecompPostcompTransport

/-!
概要：既存の下側輸送因子を、元の定値長辺の輸送比較の単位での前合成と値へ戻す。
方針：raw/native 表示・元の Hom 成分・元の単位作用を保持して同じ指定値を合成する。
規約：因子と比較を選び直さない。使われ方：元の三角形の因子消去を下側因子へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "c₀" => coherentDiagramTotalCocone F
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "I" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "e" => constantDiagramMappingTransportIso
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) I
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex c₀)) (coconeTransformationVertex c₀))
local notation "V" => QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z₃)

/-- 既存の下側因子は、同じ raw 長辺の定値輸送比較を元の単位で前合成した値。 -/
lemma coherentColimitLowerTransportFactorIso_heq_raw_unit :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (((FunctorIso.precomp e (lift (𝟙 _) (SSet.const l))).precomp u₀).postcomp V) := by
  refine (coherentColimitLowerTransportFactorIso_heq_raw_component B H).trans ?_
  exact coconeIntervalFiberHomIso_app_map_heq_unit c₀ I l V

/-- 既存の下側因子は、元の実長辺上の同じ一点比較の元の単位と値への像そのもの。 -/
lemma coherentColimitLowerTransportFactorIso_heq_constant_point :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (((coherentColimitConstantTransportPointIso B H).precomp u₀).postcomp V) := by
  refine (coherentColimitLowerTransportFactorIso_heq_raw_unit B H).trans ?_
  exact (functorIsoOfEq_precomp_postcomp_heq
    (FunctorIso.precomp e (lift (𝟙 _) (SSet.const l)))
    (coherentColimitConstantTransport_source_point B H) rfl u₀ V).symm

/-- 元の coherent 単位の表示でも、同じ下側因子は同じ一点比較の単位と値への像。 -/
lemma coherentColimitLowerTransportFactorIso_heq_constant_point_unit :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (((coherentColimitConstantTransportPointIso B H).precomp
        (leftUnstraighteningMappingVertexMap F (SSet.const (JoinCocone.vertex c₀))
          (coherentVertexOfHomotopy (coconeTransformationHomotopy c₀))).val).postcomp V) := by
  rw [coherentVertexOfHomotopy_cocone]
  exact coherentColimitLowerTransportFactorIso_heq_constant_point B H

end SerrePositivity.InfinityCategories.F2
