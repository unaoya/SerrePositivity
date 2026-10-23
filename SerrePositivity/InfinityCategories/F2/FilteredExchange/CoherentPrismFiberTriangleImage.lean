module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentPrismFiberVertices

/-!
概要：共通 prism 関手の直接の指定像を、元の実際の fiber 射を両端とする同型へ揃える。
方針：明示した実頂点の像の等式で補正し、元の実際の三角形同型と同じ型で比較する。
規約：新たな同型を選ばず直接の指定像を保持。使われ方：左右の三角形同型の合成。
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


/-- 直接の共通関手像を、元の実際の fiber 射を両端とする同型へ揃える。 -/
def coherentPrismFiberFunctor_triangleIso
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :=
  isoNormalizeEndpoints
    ((coherentPrismFiberFunctor F J b q hq
      (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).mapIso
      (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd))
    (coherentPrismFiberFunctor_obj_universal F G J x y T b q hq hd)
    (coherentPrismFiberFunctor_obj_long F G J x y T b q hq hd)

/-- 補正した直接の指定像は、元の実際の fiber 三角形同型と同じ型で等しい。 -/
lemma coherentPrismFiberFunctor_triangleIso_eq_actual
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    coherentPrismFiberFunctor_triangleIso F G J x y T b q hq hd =
      coherentTransformationTriangleFiberIso F G J x y T b := by
  have h := iso_endpoints_heq
    ((coherentPrismFiberFunctor F J b q hq
      (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)).mapIso
      (coherentRestrictedPrismComparisonIso F G J x y T b q hq hd))
    (coherentPrismFiberFunctor_obj_universal F G J x y T b q hq hd)
    (coherentPrismFiberFunctor_obj_long F G J x y T b q hq hd)
  exact eq_of_heq (h.trans (coherentPrismFiberFunctor_triangle_heq_actual F G J x y T b q hq hd))

end SerrePositivity.InfinityCategories.F2
