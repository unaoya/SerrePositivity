module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedEndpointVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallTriangleRelativePresentation

/-!
概要：正規化 prism 比較の両端を、元の指定射と二射の合成の相対関手頂点へ揃える。
方針：実終点の厳密な回収と元の普遍 prism・長辺の頂点公式を合成する。
規約：元の射と三角形を保持。使われ方：同じ型の指定同型の等式への正規化。
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
local notation "P" => relativeFunctorPre (leftUnstraighteningProjection J)
  (leftUnstraighteningProjection F) (Over.Hom.left m)
local notation "fd" => Subtype.val (leftUnstraighteningMappingVertexMap F J T.diagonal)
local notation "hfd" => Subtype.property (leftUnstraighteningMappingVertexMap F J T.diagonal)
local notation "fc" => Subtype.val (leftUnstraighteningMappingVertexMap F G x) ≫
  Subtype.val (leftUnstraighteningMappingVertexMap G J y)
local notation "hfc" => coherentTransformationMappingComposite_projection F G J x y
local notation "Z" => ((Δ[1] ◁ 𝟙 A) ⊗ₘ SSet.const T.diagonal) ≫
  leftUnstraighteningTransformationFamilyLift F J
local notation "w" => unstraighteningMappingTriangleLongWitness F G J (SSet.const x)
  (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long

/-- 普遍 prism の正規化後の終点は元の指定長射の相対関手頂点。 -/
lemma coherentRestrictedPrismEndpoint_universal
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentRestrictedPrismEndpoint F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
      (coherentRestrictedPrismUniversalVertex F G J x y T b q hq hd) =
    (P).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        fd hfd) := by
  unfold coherentRestrictedPrismUniversalVertex
  refine (coherentRestrictedPrismEndpoint_vertex F G J x y T b q hq hd Z
    (unstraighteningIdentityPrism_projection F J (SSet.const T.diagonal))
    (unstraighteningIdentityPrism_source F J (SSet.const T.diagonal))).trans ?_
  exact (restrictedUniversalEndpoint_vertex F J T.diagonal l (m).left).trans
    (relativeFunctorPre_vertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
      (m).left fd hfd).symm

/-- 実長辺の正規化後の終点は、元の二つの実射の合成の相対関手頂点。 -/
lemma coherentRestrictedPrismEndpoint_long
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentRestrictedPrismEndpoint F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
      (coherentRestrictedPrismLongVertex F G J x y T b q hq hd) =
    (P).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        fc hfc) := by
  unfold coherentRestrictedPrismLongVertex
  refine (coherentRestrictedPrismEndpoint_vertex F G J x y T b q hq hd
    (w).prism (w).projection (w).source).trans ?_
  exact (restrictedTriangleEndpoint_vertex F G J x y T.diagonal T.diagram
    T.first T.second T.long (m).left).trans
    (relativeFunctorPre_vertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
      (m).left fc hfc).symm

end SerrePositivity.InfinityCategories.F2
