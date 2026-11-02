module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceEndpointComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstPointPrismComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFiberWitnessRestrictedPrism

/-!
概要：元の定値第一辺と普遍第一辺の全終点比較を、元の指定 raw 一点比較へ値まで戻す。
方針：同じ選択空間の指定同型の像を、元の二実 prism の一点比較へ同定する。
規約：二実頂点と指定比較を保持。使われ方：第一辺比較を最後辺輸送で写す交換式。
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
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "W" => functorHomotopyPointedPrism ca (𝟙 _)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy ca))
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B a)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "w" => constantDiagramTransportWitness
  (constantDiagramMappingFamilyWitness (CategoryTheory.Functor.obj SSet.uliftFunctor B) A)

/-- 元の二実第一辺の全終点比較は、元の同じ raw 指定一点比較そのもの。 -/
lemma coherentColimitRawFirstChoiceEndpoint_specified_heq :
    HEq (VertexIso.map ((coherentColimitRawFirstChoiceSpace_isContractibleKan B a P).vertexIso
      (coherentColimitRawFirstChoiceConstantVertex B a)
      (coherentColimitRawFirstChoiceUniversalVertex B a P))
      (curry (coherentColimitRawFirstChoiceEndpoint B a P)))
      (coherentColimitConstantTransportRawPointIso B a) := by
  have hp : W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) _ ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge := by
    rw [functorHomotopyPointedPrism_projection, Category.id_comp]
    exact coherentColimitConstantPrism_base B a _
  have hs : prismEndpoint 0 _ ≫ W = P ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
    rw [functorHomotopyPointedPrism_source, Category.id_comp]
    exact (constantUnstraighteningFiberProjection_ι _ _).symm
  have hg : prismEndpoint 1 _ ≫ W = (ma ≫ PG) ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)) := by
    rw [functorHomotopyPointedPrism_target, Category.id_comp]
    simp only [Category.assoc, coherentColimitRawConstantFiberProjection,
      constantUnstraighteningFiberProjection_ι]
  have hm := coherentColimitRawFirstChoiceEndpoint_comparison_heq B a P W
    (coherentColimitRawTransportPointPrism B a P) hp
    (coherentColimitRawTransportPointPrism_projection B a P) hs
    (coherentColimitRawTransportPointPrism_start B a P) (ma ≫ PG)
    (P ≫ coherentColimitRawFiberTransport B a) hg
    (coherentColimitRawTransportPointPrism_finish B a P)
  have hS : (Δ[1] ◁ s) ≫ (pointedIntervalTransportSource P A).prism =
      coherentColimitRawTransportPointPrism B a P := by
    simpa only [Category.id_comp, coherentColimitRawTransportPointPrism] using
      pointedIntervalTransportSource_point_prism P A (𝟙 _) l
  have hr := relativeFiberWitness_heq_restrictedPrism pointedSpaceProjection P
    (intervalMappingUncurry A) (intervalMappingUncurry_one A) w
    (pointedIntervalTransportSource P A) s
    _ _ (coherentColimitRawFirstChoice_initial_base B a P)
    (coherentColimitRawFirstChoice_final_base B a P) W
    (coherentColimitRawTransportPointPrism B a P) hp
    (coherentColimitRawTransportPointPrism_projection B a P) hs
    (coherentColimitRawTransportPointPrism_start B a P) (ma ≫ PG)
    (P ≫ coherentColimitRawFiberTransport B a) hg
    (coherentColimitRawTransportPointPrism_finish B a P)
    (coherentColimitConstantTransport_point_prism B a (𝟙 _)).symm hS.symm
  have he := (heq_of_eq (coherentColimitRawFirstPointPrismComparison_eq_point B a)).symm.trans
    (functorIsoOfEq_heq _ _ _)
  exact hm.trans (hr.trans he.symm)

end SerrePositivity.InfinityCategories.F2
