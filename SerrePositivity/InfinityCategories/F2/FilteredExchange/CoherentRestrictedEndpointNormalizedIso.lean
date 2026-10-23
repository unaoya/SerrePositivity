module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedEndpointVertices

/-!
概要：共通 prism 比較の実終点の両端を、元の相対射の関手頂点へ正規化する。
方針：二つの厳密な実頂点の等式で両端を揃え、既存の正規化比較と同じ型で比較する。
規約：同じ指定像を保持。使われ方：縮小・宇宙下降後も指定値の等式として使う。
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

/-- 実終点の指定像を、元の指定射と二射の合成の相対頂点を両端とする同型に揃える。 -/
def coherentRestrictedPrismEndpointNormalizedIso
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    VertexIso ((P).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        fd hfd))
      ((P).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
          fc hfc)) :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk
    (coherentRestrictedPrismEndpoint_universal F G J x y T b q hq hd))).symm ≪≫
  VertexIso.map (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)
    (coherentRestrictedPrismEndpoint F G J x y T b q hq hd) ≪≫
  eqToIso (congrArg SSet.HomotopyCategory.mk
    (coherentRestrictedPrismEndpoint_long F G J x y T b q hq hd))

/-- 両端を揃えた共通空間からの指定終点像は、元の正規化した実際の局所比較と等しい。 -/
lemma coherentRestrictedPrismEndpointNormalizedIso_eq
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    coherentRestrictedPrismEndpointNormalizedIso F G J x y T b q hq hd =
      normalizedRestrictedTriangleIso F G J x y T.diagonal T.diagram T.first T.second T.long
        (m).left := by
  have hs := congrArg SSet.HomotopyCategory.mk
    (coherentRestrictedPrismEndpoint_universal F G J x y T b q hq hd)
  have ht := congrArg SSet.HomotopyCategory.mk
    (coherentRestrictedPrismEndpoint_long F G J x y T b q hq hd)
  have h := iso_endpoints_heq
    (VertexIso.map (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)
      (coherentRestrictedPrismEndpoint F G J x y T b q hq hd)) hs ht
  exact eq_of_heq (h.trans
    (coherentRestrictedPrismComparisonIso_endpoint_heq_normalized F G J x y T b q hq hd))

end SerrePositivity.InfinityCategories.F2
