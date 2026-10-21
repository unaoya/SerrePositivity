module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceLongComposition
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceEndpointComparison
public import SerrePositivity.InfinityCategories.F2.PointedTriangleFamilyLongEndpoint

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
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k
local notation "a₂" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "hEnd" => coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS

/-- 長辺三証拠の中間比較は、元の全族比較を長辺制限と同じ終点で写したもの。 -/
lemma coherentColimitUnitZeroFaceLongTriangleIso_heq_map :
    HEq (coherentColimitUnitZeroFaceLongTriangleIso B T k H he S hS)
      (VertexIso.map
        (VertexIso.map (coherentColimitUnitZeroFaceOriginalComparison B T k H he S hS)
          (pointedTriangleFamilyLongRestriction D))
        (pointedTriangleFamilyLongEndpointMap D Q₂ a₂ hEnd)) := by
  let w₀ := coherentColimitUnitZeroFaceLongWitness B T k H he S hS false
  let w₁ := coherentColimitUnitZeroFaceLongWitness B T k H he S hS true
  rw [pointedTriangleFamilyLongRestriction_vertexIso D
    (coherentColimitUnitZeroFaceOriginalComparison B T k H he S hS)]
  exact relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection _ _
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K)) _
    (coherentColimitUnitZeroFaceLong_base_initial B T k H he S hS)
    (prismEndpoint 1 (leftUnstraightening F ⊗ K)) Q₂ a₂
    (coherentColimitUnitZeroFaceLong_base_endpoint B T k H he S hS)
    w₀.extension w₁.extension w₀.over w₁.over w₀.initial w₁.initial
    w₀.endpoint w₁.endpoint w₀.endpoint_over w₁.endpoint_over w₀.evaluate w₁.evaluate

/-- 三証拠の中間比較は、構成済みの同じ元の native 合成への指定終点比較そのもの。 -/
lemma coherentColimitUnitZeroFaceLongTriangleIso_heq_native :
    HEq (coherentColimitUnitZeroFaceLongTriangleIso B T k H he S hS)
      (coherentColimitUnitZeroFaceEndpointIso B T k H he S hS) := by
  let e := coherentColimitUnitZeroFaceOriginalComparison B T k H he S hS
  have hc := vertexIso_map_comp e (pointedTriangleFamilyLongRestriction D)
    (pointedTriangleFamilyLongEndpointMap D Q₂ a₂ hEnd)
  have ht := vertexIso_map_heq e (pointedTriangleFamilyLongEndpoint_factor D Q₂ a₂ hEnd)
  exact (coherentColimitUnitZeroFaceLongTriangleIso_heq_map B T k H he S hS).trans
    ((heq_of_eq hc).trans (ht.trans
      (coherentColimitUnitZeroFaceEndpointIso_heq_map B T k H he S hS).symm))

/-- 同じ実終点の表示では、長辺三証拠の中間比較と元の native 比較は厳密に等しい。 -/
lemma coherentColimitUnitZeroFaceLongTriangleIso_eq_native :
    coherentColimitUnitZeroFaceLongTriangleIso B T k H he S hS =
      coherentColimitUnitZeroFaceEndpointIso B T k H he S hS :=
  eq_of_heq (coherentColimitUnitZeroFaceLongTriangleIso_heq_native B T k H he S hS)

/-- 元の指定始域比較に構成済みの native 比較を合成すると、同じ直接比較になる。 -/
lemma coherentColimitUnitZeroFaceLongSource_native_trans :
    coherentColimitUnitZeroFaceLongSourceIso B T k H he S hS ≪≫
      coherentColimitUnitZeroFaceEndpointIso B T k H he S hS =
      coherentColimitUnitZeroFaceLongCompositeIso B T k H he S hS := by
  rw [← coherentColimitUnitZeroFaceLongTriangleIso_eq_native B T k H he S hS]
  exact coherentColimitUnitZeroFaceLongIso_trans B T k H he S hS

end SerrePositivity.InfinityCategories.F2
