module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedOutputComparison

/-!
概要：共通 prism 関手の直接の指定像を、元の実際の fiber 三角形同型と比較する。
方針：小さい両端の補正を fiber Hom へ写し、終点の補正の保存と合成する。
規約：端点の等式は明示した証拠を使う。使われ方：native path 像の左右分解。
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

local notation "i" => vertexFiberι (smallLeftUnstraighteningProjection F) b
local notation "Q" => relativeFunctorBaseFiberHom (smallLeftUnstraighteningProjection J)
  (i ≫ smallLeftUnstraighteningProjection F) b
  (vertexFiberι_comp (smallLeftUnstraighteningProjection F) b)

/-- 両段階の明示した両端補正後も、同じ全 prism 関手の直接の指定像の値を保つ。 -/
lemma coherentRestrictedPrismFiberTriangleIso_heq_direct
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    HEq (coherentRestrictedPrismFiberTriangleIso F G J x y T b q hq hd)
      ((coherentPrismFiberFunctor F J b q hq
        (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).mapIso
        (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)) := by
  have hs := normalizeSmallTriangleEndpointIso_map_heq F G J x y T i
    (coherentRestrictedPrismSmallEndpointIso F G J x y T b q hq hd) Q
  have hm := coherentPrismFiberOutputFunctor_mapIso F J b
    (coherentRestrictedPrismEndpointNormalizedIso F G J x y T b q hq hd)
  exact hs.trans ((heq_of_eq hm.symm).trans
    (coherentRestrictedPrismEndpoint_output_heq_direct F G J x y T b q hq hd))

/-- 直接の関手像は、元の実際の指定 fiber 三角形同型と値まで一致する。 -/
lemma coherentPrismFiberFunctor_triangle_heq_actual
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    HEq ((coherentPrismFiberFunctor F J b q hq
      (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).mapIso
      (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd))
      (coherentTransformationTriangleFiberIso F G J x y T b) :=
  (coherentRestrictedPrismFiberTriangleIso_heq_direct F G J x y T b q hq hd).symm.trans
    (coherentRestrictedPrismFiberTriangleIso_heq_actual F G J x y T b q hq hd)

end SerrePositivity.InfinityCategories.F2
