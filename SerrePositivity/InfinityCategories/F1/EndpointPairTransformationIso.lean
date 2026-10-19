module

public import SerrePositivity.InfinityCategories.F1.EndpointPairTransformationVertices
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyComparison

/-!
概要：両端の和で図式を固定する空間と coherent な変換空間の厳密な同型。
方針：普遍変換の評価を固定境界の図式へ curry し両方向の評価を比較する。
規約：元の底は任意で全高次単体を保持する。
使われ方：固定境界での比較とパラメーター付きの変換の比較を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：普遍的な変換は両端の和の上で指定した分類図式に定値。
方針：直和の二成分で普遍変換の端点公式を使う。
規約：パラメーターは変換空間全体。
使われ方：逆向きの固定境界図式への射の構成。 -/
lemma leftUnstraighteningTransformationFamily_endpointPair {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (prismEndpointPair B ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G =
      fst (joinEndpointDiagram B B) (leftUnstraighteningTransformationSpace F G) ≫
        joinEndpointDesc F G := by
  let T := leftUnstraighteningTransformationSpace F G
  have h₀ : (prismEndpoint 0 B ▷ T) ≫ leftUnstraighteningTransformationFamily F G =
      fst B T ≫ F := leftUnstraighteningTransformationFamily_zero F G
  have h₁ : (prismEndpoint 1 B ▷ T) ≫ leftUnstraighteningTransformationFamily F G =
      fst B T ≫ G := leftUnstraighteningTransformationFamily_one F G
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨b, t⟩
  cases b with
  | inl b =>
    exact congrArg (fun k : B ⊗ T ⟶ SpaceInfinity.{u} ↦ k.app n (b, t)) h₀
  | inr b =>
    exact congrArg (fun k : B ⊗ T ⟶ SpaceInfinity.{u} ↦ k.app n (b, t)) h₁

/-- 概要：coherent な変換空間から固定境界の図式空間への射。
方針：普遍変換の評価を curry して境界制限の fiber へ持ち上げる。
規約：変換を同値類へ移さず元の図式の族を保つ。
使われ方：境界固定空間と変換空間の同型の逆方向。 -/
def transformationEndpointPairDiagramMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationSpace F G ⟶ endpointPairDiagramSpace F G :=
  vertexFiberLift _ _ (curry (leftUnstraighteningTransformationFamily F G)) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, leftUnstraighteningTransformationFamily_endpointPair,
      uncurry_const_functorVertex])

/-- 概要：固定境界の図式から変換へ戻す往復は恒等射。
方針：区間模型と prism の評価の単射性で検査する。
規約：厳密な射の一致。
使われ方：同型の一方の往復。 -/
lemma transformationEndpointPairDiagramMap_comp {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    transformationEndpointPairDiagramMap F G ≫ endpointPairDiagramTransformationMap F G = 𝟙 _ := by
  apply intervalMappingUncurry_injective (functorVertex F) (functorVertex G)
  apply functorParameterizedPrism_injective
  rw [intervalMappingUncurry_precomp, functorParameterizedPrism_parameter,
    endpointPairDiagramTransformationMap_prism, ← uncurry_natural_left,
    transformationEndpointPairDiagramMap, vertexFiberLift_ι, uncurry_curry]
  rfl

/-- 概要：変換へ移して固定境界の図式へ戻す往復は恒等射。
方針：fiber の包含と uncurry の単射性で普遍的な評価を比較する。
規約：全高次の固定境界を保つ。
使われ方：同型のもう一方の往復。 -/
lemma endpointPairDiagramTransformationMap_comp {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    endpointPairDiagramTransformationMap F G ≫ transformationEndpointPairDiagramMap F G = 𝟙 _ := by
  apply vertexFiber_hom_ext ((pre (prismEndpointPair B)).app SpaceInfinity)
    (functorVertex (joinEndpointDesc F G))
  apply uncurry_injective
  rw [Category.assoc, transformationEndpointPairDiagramMap, vertexFiberLift_ι,
    uncurry_natural_left, uncurry_curry, leftUnstraighteningTransformationFamily_parameter,
    endpointPairDiagramTransformationMap_prism, Category.id_comp]

/-- 概要：固定境界の図式空間と coherent な変換空間は厳密に同型。
方針：二つの評価を保つ射の往復を束ねる。
規約：quasicategory の同値より強い単体集合の同型。
使われ方：元の変換と表現空間の比較の同定。 -/
def endpointPairTransformationIso {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) :
    endpointPairDiagramSpace F G ≅ leftUnstraighteningTransformationSpace F G where
  hom := endpointPairDiagramTransformationMap F G
  inv := transformationEndpointPairDiagramMap F G
  hom_inv_id := endpointPairDiagramTransformationMap_comp F G
  inv_hom_id := transformationEndpointPairDiagramMap_comp F G

end SerrePositivity.InfinityCategories
