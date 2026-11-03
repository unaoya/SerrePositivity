module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRestrictedPrismData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionDataIso

/-!
概要：既存の元の prism 制限を、指定した同じ底・始点の延長空間へ正規化する。
方針：底と初期値の等式で証明成分だけを更新し、元の指定同型の像を保つ。
規約：全円柱と元の実頂点を保持。使われ方：共通 native 長辺空間との比較。
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

/-- 既存の制限空間から指定した底と同じ元の始点を持つ空間への同型。 -/
def coherentRestrictedPrismNormalizationIso (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    relativeFunctorExtensionSpace pointedSpaceProjection (prismParameterRestriction s ≫ d)
      (prismEndpoint 0 a) (s ≫ v) (by rw [Category.assoc, hv]; rfl) ≅
    relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 a) src hq :=
  relativeExtensionDataIso pointedSpaceProjection (prismParameterRestriction s ≫ d) q
    (prismEndpoint 0 a) (s ≫ v) src (by rw [Category.assoc, hv]; rfl) hq hd
    (coherentRestrictedPrism_initial F b)

/-- 元の全空間の延長を同じ prism 制限と正規化で指定の空間へ送る。 -/
def coherentRestrictedPrismNormalizedMap (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    relativeFunctorExtensionSpace pointedSpaceProjection d (prismEndpoint 0 A ▷ Δ[0]) v hv ⟶
      relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 a) src hq :=
  prismExtensionRestriction pointedSpaceProjection d v hv s ≫
    (coherentRestrictedPrismNormalizationIso F G J x y T b q hq hd).hom

/-- 元の実延長の全円柱は、共通の底へ正規化しても同じ制限を表す。 -/
lemma coherentRestrictedPrismNormalizedMap_vertex_value
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q)
    (W : (Δ[1] ⊗ A) ⊗ Δ[0] ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = d) (hW₀ : (prismEndpoint 0 A ▷ Δ[0]) ≫ W = v) :
    (((coherentRestrictedPrismNormalizedMap F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
        (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨W, hW, hW₀⟩)).val).val =
      functorVertex (prismParameterRestriction s ≫ W) := by
  change (((prismExtensionRestriction pointedSpaceProjection d v hv s).app (Opposite.op ⦋0⦌)
    (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨W, hW, hW₀⟩)).val).val = _
  exact prismExtensionRestriction_vertex_value pointedSpaceProjection d v hv s W hW hW₀

end SerrePositivity.InfinityCategories.F2
