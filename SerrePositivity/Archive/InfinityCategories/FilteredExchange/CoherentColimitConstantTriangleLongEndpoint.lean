module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleLongValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConstantDiagramTransportCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningFamilyPrismEndpoints
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningConstantFamilyMap

/-!
概要：元の定値余極限三角形の長辺輸送の終点を、元の二辺の全作用で計算する。
方針：元の長辺 prism の一致と元の終点式を使い、定値係数を同じ作用頂点へ戻す。
規約：元の二辺・全係数・実終点を保持。使われ方：下側の指定三角形比較の消去。
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
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "A" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))
local notation "R" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))

/-- 元の長辺輸送の全終点は、元の二作用と元の fiber 射影の合成そのもの。 -/
lemma coherentColimitConstantTriangleLongTransport_endpoint :
    (coherentColimitConstantTriangleLongTransport B T).endpoint =
      fst _ (Δ[0] : SSet.{u + 1}) ≫
        (leftUnstraighteningMappingVertexMap _ _ A).val ≫
          (leftUnstraighteningMappingVertexMap _ _ R).val ≫
            constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃ := by
  have he := (coherentColimitConstantTriangleLongTransport B T).finish.symm
  have hp := congrArg (fun f => prismEndpoint 1 _ ≫ f)
    (coherentColimitConstantTriangleLongTransport_prism B T)
  have ht := unstraighteningFamilyWitness_leftPrism_target
    (coherentColimitConstantTriangleLongWitness B T)
  have h := he.trans (hp.trans ht)
  simp only [unstraighteningMappingConst_uncurry, ← Category.assoc, lift_fst] at h
  apply vertexFiber_hom_ext pointedSpaceProjection z₃
  simpa only [Category.assoc, constantUnstraighteningFiberProjection_ι] using h

/-- 同じ長辺輸送の全 Hom 作用は、元の二作用と fiber 射影の合成の定値族そのもの。 -/
lemma coherentColimitConstantTriangleLongTransport_map :
    (coherentColimitConstantTriangleLongTransport B T).map =
      SSet.const (functorVertex ((leftUnstraighteningMappingVertexMap _ _ A).val ≫
        (leftUnstraighteningMappingVertexMap _ _ R).val ≫
          constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃)) := by
  apply MonoidalClosed.uncurry_injective
  rw [FiberTransportFamily.map, MonoidalClosed.uncurry_curry,
    coherentColimitConstantTriangleLongTransport_endpoint, uncurry_const_functorVertex]

/-- 元の長辺輸送を一点で評価しても、同じ二つの指定作用の合成を厳密に回収する。 -/
lemma coherentColimitConstantTriangleLongTransport_map_vertex
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    (coherentColimitConstantTriangleLongTransport B T).map.app (Opposite.op ⦋0⦌) v =
      functorVertex ((leftUnstraighteningMappingVertexMap _ _ A).val ≫
        (leftUnstraighteningMappingVertexMap _ _ R).val ≫
          constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃) := by
  rw [coherentColimitConstantTriangleLongTransport_map, constMap_vertex_value]

end SerrePositivity.InfinityCategories.F2
