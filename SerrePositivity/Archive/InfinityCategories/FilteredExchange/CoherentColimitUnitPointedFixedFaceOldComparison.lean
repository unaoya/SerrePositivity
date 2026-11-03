module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFixedFaceOldIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionWitnessComparison

/-!
概要：三証拠の直接比較を、既存の指定三角形比較の同じ長辺の終点比較へ照合する。
方針：元の二つの実 prism を保つ指定終点比較の表示式を使う。
規約：元の指定同型を保持。使われ方：元の指定三角形比較の前合成の整合式。
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
local notation "f" => fst (leftUnstraightening F) K
local notation "w" => unstraighteningMappingTriangleLongWitness F Q₁ Q₂
  (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
  (SSet.const (coherentVertexOfHomotopy c))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle S))

/-- 表示を揃えた直接比較は、元の指定三角形比較の同じ長辺の指定終点比較。 -/
lemma coherentColimitUnitPointedFixedFaceOldLongIso_heq_specified :
    HEq (coherentColimitUnitPointedFixedFaceOldLongIso B T k j hj S hS)
      (unstraighteningIdentityRestrictedEndpointIso F Q₂
        (SSet.const (coherentVertexOfHomotopy c)) (w).prism (w).source (w).projection
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) f) := by
  let w₀ := coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS false
  let w₁ := coherentColimitUnitPointedFixedFaceOldLongWitness B T k j hj S hS true
  have h := relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection _ _
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K)) _ w₁.initial_base
    (prismEndpoint 1 (leftUnstraightening F ⊗ K)) Q₂ _ w₁.endpoint_base
    w₀.extension w₁.extension w₀.over w₁.over w₀.initial w₁.initial
    w₀.endpoint w₁.endpoint w₀.endpoint_over w₁.endpoint_over w₀.evaluate w₁.evaluate
  exact h

end SerrePositivity.InfinityCategories.F2
