module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedComparisonEndpoint

/-!
概要：正規化した実延長の終点頂点を、元の同じ prism の実終点頂点へ厳密に戻す。
方針：終点評価の交換式を同じ実延長の頂点で評価する。
規約：全延長と指定底を保持。使われ方：元の射の関手頂点への両端の正規化。
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
local notation "v" => fst A Δ[0] ≫ 𝟙 A ≫ pullback.fst pointedSpaceProjection F
local notation "hv" => unstraighteningIdentityPrism_initial F J (SSet.const T.diagonal)
local notation "src" => coherentCospanFiberPointedSource F b

/-- 正規化後の実終点は、元の同じ全 prism の実終点そのもの。 -/
lemma coherentRestrictedPrismEndpoint_vertex
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q)
    (W : (Δ[1] ⊗ A) ⊗ Δ[0] ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = d) (hW₀ : (prismEndpoint 0 A ▷ Δ[0]) ≫ W = v) :
    (coherentRestrictedPrismEndpoint F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
      ((coherentRestrictedPrismNormalizedMap F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
        (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
          (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨W, hW, hW₀⟩)) =
    unstraighteningRestrictedEndpointVertex F J (SSet.const T.diagonal)
      W hW₀ hW l (m).left := by
  let r := prismExtensionRestriction pointedSpaceProjection d v hv s
  let z := relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
    (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨W, hW, hW₀⟩
  exact congrArg (fun f => f.app (Opposite.op ⦋0⦌) (r.app (Opposite.op ⦋0⦌) z))
    (coherentRestrictedPrismNormalizationIso_endpoint F G J x y T b q hq hd)

end SerrePositivity.InfinityCategories.F2
