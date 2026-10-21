module

public import SerrePositivity.InfinityCategories.F2.CoherentRestrictedPrismEndpoint
public import SerrePositivity.InfinityCategories.F2.CoherentRestrictedPrismComparison
public import SerrePositivity.InfinityCategories.F2.CoherentRestrictedChoiceEndpoint

/-!
概要：共通底へ移した局所指定比較の実終点評価を、元の実際の指定比較へ接続する。
方針：正規化と終点評価の厳密な交換を、同じ二 prism の指定同型へ適用する。
規約：元の比較・両端の表示・指定値を保持。使われ方：縮小と宇宙下降への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)
local notation "A" => leftUnstraightening F
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => Over.Hom.left m ≫ lift (𝟙 A) (SSet.const l)
local notation "d" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ Δ[0]) ≫
  functorParameterizedPrism (intervalMappingUncurry (SSet.const T.diagonal))
local notation "src" => coherentCospanFiberPointedSource F b
local notation "w" => unstraighteningMappingTriangleLongWitness F G J (SSet.const x)
  (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long

/-- 正規化した元の指定比較の終点像は、既存の同じ二 prism の指定終点比較。 -/
lemma coherentRestrictedPrismComparisonIso_endpoint_heq
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    HEq (VertexIso.map (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)
      (coherentRestrictedPrismEndpoint F G J x y T b q hq hd))
      (unstraighteningIdentityRestrictedEndpointIso F J (SSet.const T.diagonal)
        (w).prism (w).source (w).projection l (m).left) := by
  have h := coherentRestrictedPrismNormalizationIso_endpoint F G J x y T b q hq hd
  have hm := vertexIso_map_comp (coherentRestrictedPrismChoiceIso F G J x y T b)
    (coherentRestrictedPrismNormalizationIso F G J x y T b q hq hd).hom
    (coherentRestrictedPrismEndpoint F G J x y T b q hq hd)
  exact (heq_of_eq hm).trans
    ((vertexIso_map_heq (coherentRestrictedPrismChoiceIso F G J x y T b) h).trans
      (coherentRestrictedPrismChoiceIso_endpoint F G J x y T b))


/-- 同じ終点像は両端を元の実射へ揃えた正規化局所比較とも指定値で一致する。 -/
lemma coherentRestrictedPrismComparisonIso_endpoint_heq_normalized
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    HEq (VertexIso.map (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)
      (coherentRestrictedPrismEndpoint F G J x y T b q hq hd))
      (normalizedRestrictedTriangleIso F G J x y T.diagonal T.diagram T.first T.second T.long
        (m).left) :=
  (coherentRestrictedPrismComparisonIso_endpoint_heq F G J x y T b q hq hd).trans
    (normalizedRestrictedTriangleIso_heq F G J x y T.diagonal
      T.diagram T.first T.second T.long (m).left).symm

end SerrePositivity.InfinityCategories.F2
