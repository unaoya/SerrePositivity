module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.EndpointPairTransformationSpace
public import SerrePositivity.InfinityCategories.Core.FixedDiagramVertexEquiv

/-!
概要：固定境界の分類図式から変換空間への射は各頂点で元の prism を回収する。
方針：curry の頂点評価と因子の交換を計算する。
規約：厳密な頂点の一致を与える。
使われ方：境界固定の表現の比較を元の変換の比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：curry の指定頂点での値はそのパラメーターで評価した射の関手頂点。
方針：uncurry の頂点公式を関手頂点の全単射で戻す。
規約：単体集合は任意。
使われ方：二度 curry した変換空間の射の頂点計算。 -/
lemma simplicialCurry_vertex {A K X : SSet.{u}} (H : A ⊗ K ⟶ X) (x : K _⦋0⦌) :
    (curry H).app _ x = functorVertex (lift (𝟙 A) (SSet.const x) ≫ H) := by
  have h := uncurry_at_vertex (curry H) x
  rw [uncurry_curry] at h
  exact ((congrArg (functorVertexEquiv A X) h).trans
    ((functorVertexEquiv A X).apply_symm_apply _)).symm

/-- 概要：固定境界の図式 H を変換空間へ写すと H から作る実際の辺の頂点となる。
方針：curry の頂点評価、対称子、内部 Hom の頂点の往復を使う。
規約：入力の二つの端点条件と両端の和の条件を明示する。
使われ方：元の変換と復元した変換の厳密な表示の同定。 -/
lemma endpointPairDiagramTransformationMap_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (hH : prismEndpointPair B ≫ H = joinEndpointDesc F G) :
    (endpointPairDiagramTransformationMap F G).app _
      (fixedDiagramVertex (prismEndpointPair B) (joinEndpointDesc F G) H hH) =
      intervalMappingVertexOfEdge (functorEdgeFromPrism H h₀ h₁) := by
  let K := endpointPairDiagramSpace F G
  let q := vertexFiberι ((pre (prismEndpointPair B)).app SpaceInfinity)
    (functorVertex (joinEndpointDesc F G))
  let x : K _⦋0⦌ := fixedDiagramVertex (prismEndpointPair B) (joinEndpointDesc F G) H hH
  apply Subtype.ext
  change (curry (functorParameterizedCurry
    ((α_ Δ[1] B K).hom ≫ ((α_ Δ[1] B K).inv ≫ uncurry q)))).app _ x =
      functorVertex (SSet.yonedaEquiv.symm (functorEdgeFromPrism H h₀ h₁).edge)
  simp only [Iso.hom_inv_id_assoc]
  have hr : SSet.yonedaEquiv.symm (functorEdgeFromPrism H h₀ h₁).edge =
      curry ((β_ B (Δ[1] : SSet.{u + 1})).hom ≫ H) := by
    exact (SSet.yonedaEquiv (X := (ihom B).obj SpaceInfinity) (n := ⦋1⦌)).symm_apply_apply _
  rw [hr, simplicialCurry_vertex]
  apply congrArg functorVertex
  apply uncurry_injective
  rw [uncurry_natural_left, functorParameterizedCurry, uncurry_curry, uncurry_curry]
  have hn : (B ◁ lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const x)) ≫
      ((α_ B Δ[1] K).inv ≫ ((β_ B Δ[1]).hom ▷ K) ≫ uncurry q) =
        (β_ B Δ[1]).hom ≫ (lift (𝟙 (Δ[1] ⊗ B)) (SSet.const x) ≫ uncurry q) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hn, uncurry_at_vertex]
  change (β_ B Δ[1]).hom ≫ (functorVertexEquiv (Δ[1] ⊗ B) SpaceInfinity).symm
    (functorVertex H) = _
  rw [show functorVertex H = functorVertexEquiv _ _ H from rfl, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories
