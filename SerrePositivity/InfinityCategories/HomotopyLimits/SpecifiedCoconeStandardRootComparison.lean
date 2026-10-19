module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeCommonRootComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.StandardLongComparison

/-!
概要：共通根辺上の二つの標準長辺を、元の二単体による同じ点輸送へ同定する。
方針：長辺制限と底の移送が保持した実際の図式を、標準 prism の点評価と照合する。
規約：同じ根辺空間の正準比較を使う。使われ方：元の指定境界経路の中心因子。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

private lemma pointTriangle_long {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
    (σ : SSet.Edge.CompStruct e f g) (v : (vertexFiber p a) _⦋0⦌) :
    stdSimplex.δ (1 : Fin 3) ≫ coherentTransportTriangleVertex p σ v =
      prismVertexEvaluation (coherentTransportTriangleLongPrism p σ) v := by
  rw [coherentTransportTriangleVertex, prismVertexEvaluation_shape]
  rfl

private lemma contractibleComparison_endpoint_congr {X Y : SSet.{u}}
    (hX : IsContractibleKan X) (F : X ⟶ Y) {x x' y y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    Arrow.mk (VertexIso.map (hX.vertexIso x y) F).hom =
      Arrow.mk (VertexIso.map (hX.vertexIso x' y') F).hom := by
  subst x' y'
  rfl

attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "v" => SSet.yonedaEquiv.symm c
local notation "k" => stdSimplex.δ (1 : Fin 3)
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "σL" => partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "σR" => partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "βL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σL)
local notation "βR" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σR)
local notation "hvL" => specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "hvR" => specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "hv" => specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "L" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "S" => specifiedCoconeRightRootExtensionSpace hp p c hc dB dC

local notation "v₀" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "e" => partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC

/-- 同じ標準三角形の共通根辺への像は、元の長辺 prism の点評価そのもの。 -/
lemma specifiedCoconeLeftCommonRootRestriction_standard :
    (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
        (specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC) =
      coherentTransportLongPointExtensionVertex q v₀ σL := by
  let T := coherentTransportTriangleVertex q σL v₀
  have h₁ := congrArg
    (fun z ↦ (fixedExtensionBaseIso q
      (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
      a v ((hvL).trans (Category.assoc _ _ _)) hv).hom.app _ z)
    (specifiedCoconeLeftStandardTriangleExtensionVertex_long hp p c hc dB dC)
  have h₂ := fixedExtensionBaseIso_vertex q
    (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)
    a v ((hvL).trans (Category.assoc _ _ _)) hv (k ≫ T)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ k ≫ z)
      (coherentTransportTriangleVertex_projection q σL v₀)))
    ((Category.assoc _ _ _).symm.trans
      (specifiedCoconeLeftStandardTriangleExtension_initial hp p c hc dB dC))
  refine h₁.trans (h₂.trans ?_)
  apply congrArg (relativeFunctorExtensionSpaceVertexEquiv q β a v hv)
  apply Subtype.ext
  exact pointTriangle_long q σL v₀

/-- 同じ標準三角形の共通根辺への像は、元の長辺 prism の点評価そのもの。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_standard :
    (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
        (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC) =
      coherentTransportLongPointExtensionVertex q v₀ σR := by
  let T := coherentTransportTriangleVertex q σR v₀
  have h₁ := congrArg
    (fun z ↦ (fixedExtensionBaseIso q
      (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
      a v ((hvR).trans (Category.assoc _ _ _)) hv).hom.app _ z)
    (specifiedCoconeRightPrefixStandardTriangleExtensionVertex_long hp p c hc dB dC)
  have h₂ := fixedExtensionBaseIso_vertex q
    (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)
    a v ((hvR).trans (Category.assoc _ _ _)) hv (k ≫ T)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ k ≫ z)
      (coherentTransportTriangleVertex_projection q σR v₀)))
    ((Category.assoc _ _ _).symm.trans
      (specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC))
  refine h₁.trans (h₂.trans ?_)
  apply congrArg (relativeFunctorExtensionSpaceVertexEquiv q β a v hv)
  apply Subtype.ext
  exact pointTriangle_long q σR v₀

/-- 元の共通根辺上の二つの標準長辺の正準比較。 -/
def specifiedCoconeStandardRootComparisonIso :=
  (specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC).vertexIso
    ((specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
      (specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC))
    ((specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
      (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))

/-- 標準長辺間の同じ正準比較の終点は、元の native な span 合成同型の同じ成分。 -/
lemma specifiedCoconeStandardRootComparisonIso_endpoint_hom_arrow :
    Arrow.mk (VertexIso.map (specifiedCoconeStandardRootComparisonIso hp p c hc dB dC) F).hom =
      Arrow.mk ((partialColimitSpanTransportIso c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC q).toNatIso.hom.app
          (SSet.HomotopyCategory.mk v₀)) := by
  have h := contractibleComparison_endpoint_congr
    (specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC) F
    (specifiedCoconeLeftCommonRootRestriction_standard hp p c hc dB dC)
    (specifiedCoconeRightPrefixCommonRootRestriction_standard hp p c hc dB dC)
  exact h.trans (coherentTransportStandardLongComparisonIso_endpoint_hom_arrow q v₀ σL σR)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
