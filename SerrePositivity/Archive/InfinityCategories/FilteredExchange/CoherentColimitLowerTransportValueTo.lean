module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueTo
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerTransportPointValue

/-!
概要：下側輸送因子を、元の定値一点比較の固定 native 値への像として同定する。
方針：同じ raw/native 区間族の成分を、同じ指定頂点等式で一つの値へ写す。
規約：元の単位・比較を保持。使われ方：五因子式の下側因子の消去。
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
local notation "I" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "e" => constantDiagramMappingTransportIso
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) I
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex c₀)) (coconeTransformationVertex c₀))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)

/-- 下側因子は元の一点比較を元の単位で前合成し、同じ固定値へ写した指定値。 -/
lemma coherentColimitLowerTransportFactorIso_heq_constant_point_valueTo :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (((coherentColimitConstantTransportPointIso B H).precomp u₀).postcomp V) := by
  refine (coherentColimitLowerTransportFactorIso_heq_component B H).trans ?_
  refine (coconeIntervalFiberHomIso_app_valueTo_heq_of_target_eq c₀
    (coherentDiagramTotalCocone_vertex G) _ _
    (coherentColimitRawIntervalFamily_heq_native B H) l).symm.trans ?_
  refine (coconeIntervalFiberHomIso_app_map_heq_unit c₀ I l V).trans ?_
  exact (functorIsoOfEq_precomp_postcomp_heq
    (FunctorIso.precomp e (lift (𝟙 _) (SSet.const l)))
    (coherentColimitConstantTransport_source_point B H) rfl u₀ V).symm

/-- 同じ固定値への表示でも、元の coherent 単位の指定頂点をそのまま使える。 -/
lemma coherentColimitLowerTransportFactorIso_heq_constant_point_unit_valueTo :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (((coherentColimitConstantTransportPointIso B H).precomp
        (leftUnstraighteningMappingVertexMap F (SSet.const (JoinCocone.vertex c₀))
          (coherentVertexOfHomotopy (coconeTransformationHomotopy c₀))).val).postcomp V) := by
  rw [coherentVertexOfHomotopy_cocone]
  exact coherentColimitLowerTransportFactorIso_heq_constant_point_valueTo B H

end SerrePositivity.InfinityCategories.F2
