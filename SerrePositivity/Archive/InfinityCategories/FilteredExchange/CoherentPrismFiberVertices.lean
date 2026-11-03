module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRestrictedDirectFiberComparison

/-!
概要：共通 prism 関手による実頂点の像を、元の実際の fiber 射の関手頂点へ同定する。
方針：実終点・縮小・下降の頂点公式を、元の fiber Hom の厳密な頂点公式へ接続する。
規約：元の射と全三角形を保持。使われ方：左右の指定同型を合成する際の両端補正。
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

local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pJ" => smallLeftUnstraighteningProjection J
local notation "i" => vertexFiberι pF b
local notation "Q" => relativeFunctorBaseFiberHom pJ (i ≫ pF) b (vertexFiberι_comp pF b)

/-- 普遍 prism の像は元の指定長射の実際の fiber 射の関手頂点。 -/
lemma coherentPrismFiberFunctor_obj_universal
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentPrismFiberFunctor F J b q hq
      (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).obj
      (SSet.HomotopyCategory.mk (coherentRestrictedPrismUniversalVertex F G J x y T b q hq hd)) =
    SSet.HomotopyCategory.mk (functorVertex (vertexFiberMap pF pJ
      (coherentTransformationTotalMap F J T.diagonal)
      (coherentTransformationTotalMap_projection F J T.diagonal) b)) := by
  rw [coherentPrismFiberFunctor_obj_vertex]
  change SSet.HomotopyCategory.mk ((Q).app (Opposite.op ⦋0⦌)
    (((coherentPrismEndpointShrink F J b).app (Opposite.op ⦋0⦌)
      ((coherentRestrictedPrismEndpoint F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
        (coherentRestrictedPrismUniversalVertex F G J x y T b q hq hd))).down)) = _
  rw [coherentRestrictedPrismEndpoint_universal]
  change SSet.HomotopyCategory.mk ((Q).app (Opposite.op ⦋0⦌)
    (smallRestrictedEndpointVertex F J (leftUnstraighteningMappingVertexMap F J T.diagonal).val
      (leftUnstraighteningMappingVertexMap F J T.diagonal).property i)) = _
  rw [smallRestrictedEndpointVertex_eq]
  exact congrArg SSet.HomotopyCategory.mk (relativeFunctorBaseFiberHom_pre_vertex pF pJ b
    (coherentTransformationTotalMap F J T.diagonal)
    (coherentTransformationTotalMap_projection F J T.diagonal))

/-- 元の実長辺の像は、元の二つの実全空間射の合成の fiber 射の関手頂点。 -/
lemma coherentPrismFiberFunctor_obj_long
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentPrismFiberFunctor F J b q hq
      (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).obj
      (SSet.HomotopyCategory.mk (coherentRestrictedPrismLongVertex F G J x y T b q hq hd)) =
    SSet.HomotopyCategory.mk (functorVertex (vertexFiberMap pF pJ
      (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y)
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection]) b)) := by
  rw [coherentPrismFiberFunctor_obj_vertex]
  change SSet.HomotopyCategory.mk ((Q).app (Opposite.op ⦋0⦌)
    (((coherentPrismEndpointShrink F J b).app (Opposite.op ⦋0⦌)
      ((coherentRestrictedPrismEndpoint F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
        (coherentRestrictedPrismLongVertex F G J x y T b q hq hd))).down)) = _
  rw [coherentRestrictedPrismEndpoint_long]
  change SSet.HomotopyCategory.mk ((Q).app (Opposite.op ⦋0⦌)
    (smallRestrictedEndpointVertex F J
      ((leftUnstraighteningMappingVertexMap F G x).val ≫
        (leftUnstraighteningMappingVertexMap G J y).val)
      (coherentTransformationMappingComposite_projection F G J x y) i)) = _
  rw [smallRestrictedEndpointVertex_eq, coherentTransformationComposite_relativeVertex]
  exact congrArg SSet.HomotopyCategory.mk (relativeFunctorBaseFiberHom_pre_vertex pF pJ b
    (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y)
    (by rw [Category.assoc, coherentTransformationTotalMap_projection,
      coherentTransformationTotalMap_projection]))

end SerrePositivity.InfinityCategories.F2
