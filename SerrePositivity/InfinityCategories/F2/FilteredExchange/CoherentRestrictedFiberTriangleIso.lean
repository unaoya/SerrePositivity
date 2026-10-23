module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedSmallEndpointIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleFiberEndpoint

/-!
概要：共通 prism の実指定比較を、元の実際の fiber 三角形同型へ両端を保って接続する。
方針：同じ縮小・下降後の同型を小さい実頂点へ正規化し、元の fiber Hom へ写す。
規約：元の三角形と指定値を保持。使われ方：native 指定可換性と模型 fiber 比較の照合。
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

local notation "i" => vertexFiberι (smallLeftUnstraighteningProjection F) b

local notation "Q" => relativeFunctorBaseFiberHom (smallLeftUnstraighteningProjection J)
  (i ≫ smallLeftUnstraighteningProjection F) b
  (vertexFiberι_comp (smallLeftUnstraighteningProjection F) b)

/-- 共通 prism の元の指定比較を、終点・縮小・下降・両端正規化・fiber Hom へ通す。 -/
def coherentRestrictedPrismFiberTriangleIso
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :=
  VertexIso.map (normalizeSmallTriangleEndpointIso F G J x y T i
    (coherentRestrictedPrismSmallEndpointIso F G J x y T b q hq hd)) Q

/-- その同じ指定像は、元の実際の fiber 三角形の関手同型と指定値で一致する。 -/
lemma coherentRestrictedPrismFiberTriangleIso_heq_actual
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    HEq (coherentRestrictedPrismFiberTriangleIso F G J x y T b q hq hd)
      (coherentTransformationTriangleFiberIso F G J x y T b) := by
  unfold coherentRestrictedPrismFiberTriangleIso
  rw [coherentRestrictedPrismSmallEndpointIso_eq]
  exact (coherentTransformationTriangleFiberIso_heq_endpoint F G J x y T b).symm

end SerrePositivity.InfinityCategories.F2
