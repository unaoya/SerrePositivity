module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceLongComposition
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceEndpointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFamilyLongEndpoint

/-!
概要：三証拠の中間の長辺比較は、構成済みの元の native 合成への終点比較と値まで一致。
方針：長辺制限先の可縮性と終点評価の厳密な因子分解で、元の全族比較へ戻す。
規約：元の指定同型を保持。使われ方：三証拠の合成式の native 比較側の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "D" => coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS
local notation "a₂" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "hEnd" => coherentColimitUnitPointedFixedFaceBase_endpoint B T k j hj S hS

/-- 長辺三証拠の中間比較は、元の全族比較を長辺制限と同じ終点で写したもの。 -/
lemma coherentColimitUnitPointedFixedFaceLongTriangleIso_heq_map :
    HEq (coherentColimitUnitPointedFixedFaceLongTriangleIso B T k j hj S hS)
      (VertexIso.map
        (VertexIso.map (coherentColimitUnitPointedFixedFaceOriginalComparison B T k j hj S hS)
          (pointedTriangleFamilyLongRestriction D))
        (pointedTriangleFamilyLongEndpointMap D Q₂ a₂ hEnd)) := by
  let w₀ := coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS false
  let w₁ := coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS true
  rw [pointedTriangleFamilyLongRestriction_vertexIso D
    (coherentColimitUnitPointedFixedFaceOriginalComparison B T k j hj S hS)]
  exact relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection _ _
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K)) _
    w₀.initial_base
    (prismEndpoint 1 (leftUnstraightening F ⊗ K)) Q₂ a₂
    w₀.endpoint_base
    w₀.extension w₁.extension w₀.over w₁.over w₀.initial w₁.initial
    w₀.endpoint w₁.endpoint w₀.endpoint_over w₁.endpoint_over w₀.evaluate w₁.evaluate

/-- 三証拠の中間比較は、構成済みの同じ元の native 合成への指定終点比較そのもの。 -/
lemma coherentColimitUnitPointedFixedFaceLongTriangleIso_heq_native :
    HEq (coherentColimitUnitPointedFixedFaceLongTriangleIso B T k j hj S hS)
      (coherentColimitUnitPointedFixedFaceEndpointIso B T k j hj S hS) := by
  let e := coherentColimitUnitPointedFixedFaceOriginalComparison B T k j hj S hS
  have hc := vertexIso_map_comp e (pointedTriangleFamilyLongRestriction D)
    (pointedTriangleFamilyLongEndpointMap D Q₂ a₂ hEnd)
  have ht := vertexIso_map_heq e (pointedTriangleFamilyLongEndpoint_factor D Q₂ a₂ hEnd)
  exact (coherentColimitUnitPointedFixedFaceLongTriangleIso_heq_map B T k j hj S hS).trans
    ((heq_of_eq hc).trans (ht.trans
      (coherentColimitUnitPointedFixedFaceEndpointIso_heq_map B T k j hj S hS).symm))

/-- 同じ実終点の表示では、長辺三証拠の中間比較と元の native 比較は厳密に等しい。 -/
lemma coherentColimitUnitPointedFixedFaceLongTriangleIso_eq_native :
    coherentColimitUnitPointedFixedFaceLongTriangleIso B T k j hj S hS =
      coherentColimitUnitPointedFixedFaceEndpointIso B T k j hj S hS :=
  eq_of_heq (coherentColimitUnitPointedFixedFaceLongTriangleIso_heq_native B T k j hj S hS)

/-- 元の指定始域比較に構成済みの native 比較を合成すると、同じ直接比較になる。 -/
lemma coherentColimitUnitPointedFixedFaceLongSource_native_trans :
    coherentColimitUnitPointedFixedFaceLongSourceIso B T k j hj S hS ≪≫
      coherentColimitUnitPointedFixedFaceEndpointIso B T k j hj S hS =
      coherentColimitUnitPointedFixedFaceLongCompositeIso B T k j hj S hS := by
  rw [← coherentColimitUnitPointedFixedFaceLongTriangleIso_eq_native B T k j hj S hS]
  exact coherentColimitUnitPointedFixedFaceLongIso_trans B T k j hj S hS

end SerrePositivity.InfinityCategories.F2
