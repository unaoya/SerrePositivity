module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleCanonicalOldLong
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionWitnessComparison

/-!
概要：元の全三角形の長辺比較を、元の指定相対三角形比較の前合成へ値まで同定する。
方針：同じ元の長辺証拠の終点評価を経由し、F1 指定比較の制限公式へ接続する。
規約：元の指定値を保持。使われ方：長辺の自然性から元の指定三角形比較を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "V" => coherentTriangleOfFunctorTriangle T
local notation "L" => unstraighteningMappingTriangleLongWitness F G J
  (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
  (SSet.const (coherentVertexOfHomotopy c))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle T))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle T))

/-- 同じ全係数の直接比較は、元の指定三角形比較の同じ長辺の指定終点比較。 -/
lemma functorTriangleCanonicalOldLongIso_heq_specified :
    HEq (functorTriangleCanonicalOldLongIso T p s hi)
      (unstraighteningIdentityRestrictedEndpointIso F J
        (SSet.const (coherentVertexOfHomotopy c)) (L).prism (L).source (L).projection
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) s) := by
  let w₀ := functorTriangleCanonicalOldLongWitness T p s hi false
  let w₁ := functorTriangleCanonicalOldLongWitness T p s hi true
  have h := relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection _ _
    (prismEndpoint_zero_leftAnodyne C) _ w₁.initial_base
    (prismEndpoint 1 C) J _ w₁.endpoint_base
    w₀.extension w₁.extension w₀.over w₁.over w₀.initial w₁.initial
    w₀.endpoint w₁.endpoint w₀.endpoint_over w₁.endpoint_over w₀.evaluate w₁.evaluate
  exact h

/-- 元の全三角形の長辺比較は、元の相対三角形比較の同じ前合成の値。 -/
lemma functorTriangleCanonicalLongSourceIso_heq_triangle :
    HEq (functorHomotopySourceEndpointIso c p s hi
      (functorTrianglePointedCanonicalWitness T p s hi).longWitness)
      (VertexIso.map (unstraighteningTriangleRelativeVertexIso F G J
        (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
        (V).diagram (V).first (V).second (V).long)
        (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
          s)) :=
  (functorTriangleCanonicalLongSourceIso_heq_old T p s hi).trans
    ((functorTriangleCanonicalOldLongIso_heq_specified T p s hi).trans
      (functorTrianglePointedLift_comparison_pre T s).symm)

end SerrePositivity.InfinityCategories.F2
