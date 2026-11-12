module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRestrictedFiberTriangleIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismFiberOutputFunctor
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization

/-!
概要：終点で両端を揃えた指定像と、共通 prism 関手の直接の指定像を比較する。
方針：明示した二端点の等式を後段の同じ関手へ写し、両端補正の値の保存を使う。
規約：元の指定同型と端点の証拠を保持。使われ方：直接の native path 像との照合。
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

/-- 終点での両端の補正を縮小・下降へ写しても、全 prism 関手の直接の指定像と一致。 -/
lemma coherentRestrictedPrismEndpoint_output_heq_direct
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    HEq ((coherentPrismFiberOutputFunctor F J b).mapIso
      (coherentRestrictedPrismEndpointNormalizedIso F G J x y T b q hq hd))
      ((coherentPrismFiberFunctor F J b q hq
        (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).mapIso
        (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)) := by
  have h := isoNormalizeEndpoints_map_heq (coherentPrismFiberOutputFunctor F J b)
    (VertexIso.map (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)
      (coherentRestrictedPrismEndpoint F G J x y T b q hq hd))
    (congrArg SSet.HomotopyCategory.mk
      (coherentRestrictedPrismEndpoint_universal F G J x y T b q hq hd))
    (congrArg SSet.HomotopyCategory.mk
      (coherentRestrictedPrismEndpoint_long F G J x y T b q hq hd))
  have hm := coherentPrismFiberFunctor_mapIso_output F J b q hq
    (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)
    (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd)
  exact h.trans (heq_of_eq hm.symm)

end SerrePositivity.InfinityCategories.F2
