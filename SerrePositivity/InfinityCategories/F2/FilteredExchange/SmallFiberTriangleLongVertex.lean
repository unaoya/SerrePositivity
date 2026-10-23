module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberPointedTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleExtensionVertexRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningIdentityPrismData

/-!
概要：小さい fiber の局所延長比較の第二頂点が元の全三角形の長辺を表すことを照合する。
方針：実延長の制限の頂点値と、同じ全三角形の長辺の厳密な制限式を合成する。
規約：元の長辺と全二単体を保持。使われ方：局所比較と各点の錐の二次整合の接続。
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
local notation "C" => vertexFiber (smallLeftUnstraighteningProjection F) b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => Over.Hom.left m ≫ lift (𝟙 A) (SSet.const l)
local notation "d" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ Δ[0]) ≫
  functorParameterizedPrism (intervalMappingUncurry (SSet.const T.diagonal))
local notation "v" => fst A Δ[0] ≫ 𝟙 A ≫ pullback.fst pointedSpaceProjection F
local notation "hv" => unstraighteningIdentityPrism_initial F J (SSet.const T.diagonal)
local notation "w" => unstraighteningMappingTriangleLongWitness F G J (SSet.const x)
  (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long

/-- 局所延長比較の第二実頂点は同じ全 pointed 三角形の長辺を表す。 -/
lemma coherentSmallFiberTriangleExtension_long_vertex :
    (((prismExtensionRestriction pointedSpaceProjection d v hv s).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
        (prismEndpoint 0 A ▷ (Δ[0] : SSet.{u + 1})) v hv
        ⟨(w).prism, (w).projection, (w).source⟩)).val).val =
      functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ (SSet.uliftFunctor.{u + 1, u}).obj C) ≫
        coherentSmallFiberPointedTriangle F G J x y T b) := by
  rw [prismExtensionRestriction_vertex_value pointedSpaceProjection d v hv s
    (w).prism (w).projection (w).source]
  exact congrArg functorVertex (coherentSmallFiberPointedTriangle_long F G J x y T b).symm

end SerrePositivity.InfinityCategories.F2
