module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRestrictedPrismNormalization

/-!
概要：元の普遍 prism と全三角形の長辺を、正規化した同じ選択空間の実頂点へ移す。
方針：既存の実延長の頂点表示を同じ制限写像へ入力し、全円柱の値を照合する。
規約：二つの証拠も実頂点も再選択しない。使われ方：元の局所比較の指定値の接続。
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
local notation "Z" => ((Δ[1] ◁ 𝟙 A) ⊗ₘ SSet.const T.diagonal) ≫
  leftUnstraighteningTransformationFamilyLift F J
local notation "w" => unstraighteningMappingTriangleLongWitness F G J (SSet.const x)
  (SSet.const y) (SSet.const T.diagonal) T.diagram T.first T.second T.long

/-- 元の普遍 prism の実頂点を、制限・正規化後の同じ選択空間へ移す。 -/
def coherentRestrictedPrismUniversalVertex
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 a) src hq) _⦋0⦌ :=
  (coherentRestrictedPrismNormalizedMap F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
    (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 A ▷ Δ[0]) v hv
      ⟨Z, unstraighteningIdentityPrism_projection F J (SSet.const T.diagonal),
        unstraighteningIdentityPrism_source F J (SSet.const T.diagonal)⟩)

/-- 普遍 prism の実際の全制限円柱を同じ頂点から回収する。 -/
lemma coherentRestrictedPrismUniversalVertex_value
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentRestrictedPrismUniversalVertex F G J x y T b q hq hd).val.val =
      functorVertex (prismParameterRestriction s ≫ Z) :=
  coherentRestrictedPrismNormalizedMap_vertex_value F G J x y T b q hq hd Z
    (unstraighteningIdentityPrism_projection F J (SSet.const T.diagonal))
    (unstraighteningIdentityPrism_source F J (SSet.const T.diagonal))

/-- 元の全三角形の長辺の実頂点を同じ制限・正規化へ送る。 -/
def coherentRestrictedPrismLongVertex
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (relativeFunctorExtensionSpace pointedSpaceProjection q (prismEndpoint 0 a) src hq) _⦋0⦌ :=
  (coherentRestrictedPrismNormalizedMap F G J x y T b q hq hd).app (Opposite.op ⦋0⦌)
    (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨(w).prism, (w).projection, (w).source⟩)

/-- この実頂点は元の小さい fiber 上の全三角形の同じ長辺円柱を表す。 -/
lemma coherentRestrictedPrismLongVertex_value
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    (coherentRestrictedPrismLongVertex F G J x y T b q hq hd).val.val =
      functorVertex ((stdSimplex.δ (1 : Fin 3) ▷ a) ≫
        coherentSmallFiberPointedTriangle F G J x y T b) := by
  change (((prismExtensionRestriction pointedSpaceProjection d v hv s).app (Opposite.op ⦋0⦌)
    (relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
      (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨(w).prism, (w).projection, (w).source⟩)).val).val = _
  exact coherentSmallFiberTriangleExtension_long_vertex F G J x y T b

end SerrePositivity.InfinityCategories.F2
