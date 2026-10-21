module

public import SerrePositivity.InfinityCategories.F2.CoherentRestrictedEndpointNormalizedIso
public import SerrePositivity.InfinityCategories.F2.PrismFiberHomotopyFunctor
public import SerrePositivity.InfinityCategories.F2.NormalizedSmallTriangleEndpoint

/-!
概要：両端を揃えた共通 prism の指定終点像を同じ縮小・宇宙下降へ通す。
方針：元の正規化比較との同じ型の等式を、そのまま既存の縮小・下降の写像へ適用する。
規約：指定値の等式を保持。使われ方：元の小さい fiber 比較への最終の両端正規化。
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

/-- 元の実頂点を両端とする指定終点比較を、同じ縮小と宇宙下降へ通した実同型。 -/
def coherentRestrictedPrismSmallEndpointIso
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    VertexIso (smallRestrictedEndpointVertex F J fd hfd i)
      (smallRestrictedEndpointVertex F J fc hfc i) :=
  downVertexIso (VertexIso.map (coherentRestrictedPrismEndpointNormalizedIso F G J x y T b q hq hd)
    (coherentPrismEndpointShrink F J b))

/-- 共通空間からの同じ指定像の下降は、元の既存の小さい局所比較に等しい。 -/
lemma coherentRestrictedPrismSmallEndpointIso_eq
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    coherentRestrictedPrismSmallEndpointIso F G J x y T b q hq hd =
      smallRestrictedTriangleEndpointIso F G J x y T i := by
  unfold coherentRestrictedPrismSmallEndpointIso
  rw [coherentRestrictedPrismEndpointNormalizedIso_eq]
  rfl

end SerrePositivity.InfinityCategories.F2
