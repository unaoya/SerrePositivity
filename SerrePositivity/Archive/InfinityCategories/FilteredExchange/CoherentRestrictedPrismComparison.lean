module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRestrictedPrismVertices

/-!
概要：既存の同じ二 prism の局所指定比較を、正規化した長辺空間へ写す。
方針：元の制限空間の標準比較を同じ正規化同型へ写す。
規約：同型を選び直さず指定像を構成。使われ方：元の fiber 同型と native 可換性の接続。
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

/-- 既存の同じ二 prism の制限空間内の指定比較。終点評価前の値を固定する。 -/
def coherentRestrictedPrismChoiceIso :=
  let r := prismExtensionRestriction pointedSpaceProjection d v hv s
  let z := relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
    (prismEndpoint 0 A ▷ Δ[0]) v hv
    ⟨Z, unstraighteningIdentityPrism_projection F J (SSet.const T.diagonal),
      unstraighteningIdentityPrism_source F J (SSet.const T.diagonal)⟩
  let t := relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection d
    (prismEndpoint 0 A ▷ Δ[0]) v hv ⟨(w).prism, (w).projection, (w).source⟩
  let hr := relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection
    (prismParameterRestriction s ≫ d) (prismEndpoint 0 a) (prismEndpoint_zero_leftAnodyne a)
    (s ≫ v) (by rw [Category.assoc, hv]; rfl)
  hr.vertexIso (r.app (Opposite.op ⦋0⦌) z) (r.app (Opposite.op ⦋0⦌) t)

/-- 同じ二つの実 prism の制限後の局所指定比較の、正規化同型による直接の像。 -/
def coherentRestrictedPrismComparisonIso
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    VertexIso (coherentRestrictedPrismUniversalVertex F G J x y T b q hq hd)
      (coherentRestrictedPrismLongVertex F G J x y T b q hq hd) :=
  VertexIso.map (coherentRestrictedPrismChoiceIso F G J x y T b)
    (coherentRestrictedPrismNormalizationIso F G J x y T b q hq hd).hom

/-- 元の局所指定比較の直接の像は、同じ実頂点間の標準比較の指定値に等しい。 -/
lemma coherentRestrictedPrismComparisonIso_eq
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hd : prismParameterRestriction s ≫ d = q) :
    coherentRestrictedPrismComparisonIso F G J x y T b q hq hd =
      (relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection q
        (prismEndpoint 0 a) (prismEndpoint_zero_leftAnodyne a) src hq).vertexIso
        (coherentRestrictedPrismUniversalVertex F G J x y T b q hq hd)
        (coherentRestrictedPrismLongVertex F G J x y T b q hq hd) := by
  have h := relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection q
    (prismEndpoint 0 a) (prismEndpoint_zero_leftAnodyne a) src hq
  have := h.kanComplex
  apply Iso.ext
  have ht := h.isTerminalVertex (coherentRestrictedPrismLongVertex F G J x y T b q hq hd)
  exact ht.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.F2
