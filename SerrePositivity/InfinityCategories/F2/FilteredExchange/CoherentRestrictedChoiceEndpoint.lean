module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedPrismEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedPrismComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.NormalizedRestrictedTriangle

/-!
概要：元の選択空間の指定同型の実終点像を、既存の指定終点同型として回収する。
方針：同じ二 prism と同じ標準比較の定義を明示する。
規約：元の指定値を保持。使われ方：正規化と終点評価の交換式との合成。
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
local notation "w" => unstraighteningMappingTriangleLongWitness F G J (SSet.const x)
  (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long

local notation "v" => fst A Δ[0] ≫ 𝟙 A ≫ pullback.fst pointedSpaceProjection F
local notation "hv" => unstraighteningIdentityPrism_initial F J (SSet.const T.diagonal)
local notation "c" => s ≫ (fst A Δ[0] ≫ leftUnstraighteningProjection F)
local notation "hj" => prismExtensionPullbackRestriction_endpoint d s J
  (fst A Δ[0] ≫ leftUnstraighteningProjection F)
  (unstraighteningIdentityPrism_endpoint F J (SSet.const T.diagonal))

/-- 元の局所選択空間の実際の終点評価。底の引き戻しの逆も元の指定のまま。 -/
def coherentRestrictedPrismOriginalEndpoint :
    relativeFunctorExtensionSpace pointedSpaceProjection (prismParameterRestriction s ≫ d)
      (prismEndpoint 0 a) (s ≫ v) (by rw [Category.assoc, hv]; rfl) ⟶
    relativeFunctorSpace (leftUnstraighteningProjection J) c :=
  relativeFunctorExtensionEndpoint pointedSpaceProjection (prismParameterRestriction s ≫ d)
    (prismEndpoint 0 a) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
    (prismEndpoint 1 a) J c hj

/-- 元の選択空間の同じ指定比較を評価すると、既存の指定終点比較を厳密に回収する。 -/
lemma coherentRestrictedPrismChoiceIso_endpoint :
    HEq (VertexIso.map (coherentRestrictedPrismChoiceIso F G J x y T b)
      (coherentRestrictedPrismOriginalEndpoint F G J x y T b))
      (unstraighteningIdentityRestrictedEndpointIso F J (SSet.const T.diagonal)
        (w).prism (w).source (w).projection l (m).left) := by
  rfl

end SerrePositivity.InfinityCategories.F2
