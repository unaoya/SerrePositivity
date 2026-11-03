module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRestrictedPrismNormalization
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionDataEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismExtensionPullbackRestriction

/-!
概要：正規化した prism 選択空間の実際の終点を、元の unstraightening の相対空間で読む。
方針：元の終点の底の式を同じ底の等式で移し、引き戻し終点評価を適用する。
規約：元の標的と底の射を保持。使われ方：局所指定比較の終点・縮小・下降との接続。
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
local notation "c" => s ≫ (fst A Δ[0] ≫ leftUnstraighteningProjection F)
local notation "hj" => prismExtensionPullbackRestriction_endpoint d s J
  (fst A Δ[0] ≫ leftUnstraighteningProjection F)
  (unstraighteningIdentityPrism_endpoint F J (SSet.const T.diagonal))

/-- 同じ底の等式による正規化後も、元の引き戻し標的の終点を被覆する。 -/
lemma coherentRestrictedPrismEndpoint_projection
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hd : prismParameterRestriction s ≫ d = q) : prismEndpoint 1 a ≫ q = c ≫ J := by
  rw [← hd]
  exact hj

/-- 正規化した選択空間から元の標的の相対関手空間への、実際の引き戻し終点評価。 -/
def coherentRestrictedPrismEndpoint
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 a) src hq ⟶
      relativeFunctorSpace (leftUnstraighteningProjection J) c :=
  relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq
    (prismEndpoint 1 a) J c (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)

/-- 正規化と実際の終点評価の厳密な交換式。元の底変換の逆も含む。 -/
lemma coherentRestrictedPrismNormalizationIso_endpoint
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentRestrictedPrismNormalizationIso F G J x y T b q hq hd).hom ≫
      coherentRestrictedPrismEndpoint F G J x y T b q hq hd =
    relativeFunctorExtensionEndpoint pointedSpaceProjection (prismParameterRestriction s ≫ d)
      (prismEndpoint 0 a) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
      (prismEndpoint 1 a) J c hj :=
  relativeExtensionDataIso_endpoint pointedSpaceProjection (prismParameterRestriction s ≫ d) q
    (prismEndpoint 0 a) (s ≫ v) src (by rw [Category.assoc, hv]; rfl) hq hd
    (coherentRestrictedPrism_initial F b) (prismEndpoint 1 a) J c hj
    (coherentRestrictedPrismEndpoint_projection F G J x y T b q hd)

end SerrePositivity.InfinityCategories.F2
