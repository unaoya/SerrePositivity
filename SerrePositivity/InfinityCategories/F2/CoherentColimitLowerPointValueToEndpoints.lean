module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerValueToEndpoints
public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerTransportValueTo

/-!
概要：同じ定値一点比較の単位と固定値への像の両端を、下側因子の実両端へ戻す。
方針：元の Hom 成分の実一点座標と、同じ長辺作用の実射の等式を使う。
規約：元の単位と指定比較を保持。使われ方：下側輸送因子の値までの厳密な同定。
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
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "a" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "u₀" => Subtype.val (leftUnstraighteningMappingVertexMap F
  (SSet.const (JoinCocone.vertex c₀)) (coconeTransformationVertex c₀))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex G)
local notation "M" => uncurry ((constantDiagramTransformation
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) a ≫
    leftUnstraighteningMappingSpaceMap (SSet.const (JoinCocone.vertex c₀)) (SSet.const z)) ≫
      Iso.hom (constantUnstraighteningRelativeIso
        (leftUnstraighteningProjection (SSet.const (JoinCocone.vertex c₀))) z))
local notation "C" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H))

/-- 元の一点比較を単位と固定値で写した始点は、下側因子の同じ実始点。 -/
lemma coherentColimitLowerPoint_source_valueTo_vertex :
    functorVertex ((u₀ ≫ (leftUnstraighteningMappingVertexMap _ _ C).val ≫
      constantUnstraighteningFiberProjection (CategoryTheory.Functor.obj SSet.uliftFunctor B) z)
        ≫ V) = functorVertex (coherentColimitLowerCompositeAction B H) := by
  have h := congrArg (fun x => ((ihom (leftUnstraightening F)).map V).app (Opposite.op ⦋0⦌) x)
    (coconeIntervalFiberHomIso_source_point_vertex c₀ a l)
  have hr := h.symm.trans (coherentColimitLowerRaw_source_valueTo_vertex B H)
  change functorVertex ((u₀ ≫ s ≫ M) ≫ V) = _ at hr
  have hs := congrArg (fun f => functorVertex ((u₀ ≫ f) ≫ V))
    (coherentColimitConstantTransport_source_point B H)
  simp only [Category.assoc] at hr hs ⊢
  exact hs.symm.trans hr

/-- 元の一点比較を単位と固定値で写した終点は、同じ実 fiber 輸送の終点。 -/
lemma coherentColimitLowerPoint_target_valueTo_vertex :
    functorVertex ((u₀ ≫ s ≫
      (constantUnstraighteningFiberProjection
        (CategoryTheory.Functor.obj SSet.uliftFunctor B) (JoinCocone.vertex c₀) ▷ Δ[0]) ≫
          (pointedIntervalTransport a).endpoint) ≫ V) =
      functorVertex (coconeFiberMap c₀ ≫ coherentColimitFiberTransport B H ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) := by
  have h := congrArg (fun x => ((ihom (leftUnstraightening F)).map V).app (Opposite.op ⦋0⦌) x)
    (coconeIntervalFiberHomIso_target_point_vertex c₀ a l)
  exact h.symm.trans (coherentColimitLowerRaw_target_valueTo_vertex B H)

/-- 元の二実端点だけを揃えた同じ一点比較は、下側輸送因子そのもの。 -/
lemma coherentColimitLowerPoint_valueTo_eq_lowerFactor :
    vertexIsoOfEq (((coherentColimitConstantTransportPointIso B H).precomp u₀).postcomp V)
      (coherentColimitLowerPoint_source_valueTo_vertex B H)
      (coherentColimitLowerPoint_target_valueTo_vertex B H) =
        coherentColimitLowerTransportFactorIso B H := by
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitLowerTransportFactorIso_heq_constant_point_valueTo B H).symm)

end SerrePositivity.InfinityCategories.F2
