module

public import SerrePositivity.InfinityCategories.F1.Simplicial.PrismEndpointPairPullback
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFamilyCurry
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEdgeFromPrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertices
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyVertices

/-!
概要：両端の和で分類図式を固定した空間を coherent な変換空間へ移す。
方針：図式の普遍族を二度 curry し境界の二成分で端点条件を検査する。
規約：境界固定は全高次単体で保つ。
使われ方：表現空間の可縮性による変換の左逆の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：両端の和で固定した関手空間の族の評価は二つの端点を固定する。
方針：制限の条件を uncurry して直和の二成分で評価する。
規約：標的 X とパラメーター K は任意。
使われ方：固定境界図式から変換空間への curry の入力条件。 -/
lemma endpointPairDiagramFamily_endpoints {B K X : SSet.{u}} (F G : B ⟶ X)
    (q : K ⟶ (ihom ((Δ[1] : SSet.{u}) ⊗ B)).obj X)
    (hq : q ≫ (pre (prismEndpointPair B)).app X =
      SSet.const (functorVertex (joinEndpointDesc F G))) :
    prismEndpoint 0 (B ⊗ K) ≫ ((α_ Δ[1] B K).inv ≫ uncurry q) = fst B K ≫ F ∧
    prismEndpoint 1 (B ⊗ K) ≫ ((α_ Δ[1] B K).inv ≫ uncurry q) = fst B K ≫ G := by
  have h : (prismEndpointPair B ▷ K) ≫ uncurry q =
      fst (joinEndpointDiagram B B) K ≫ joinEndpointDesc F G := by
    rw [← uncurry_pre_app, hq, uncurry_const_functorVertex]
  constructor
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨b, k⟩
    exact ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app h n)
      ((Sum.inl b, k) : (joinEndpointDiagram B B ⊗ K).obj n)
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨b, k⟩
    exact ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app h n)
      ((Sum.inr b, k) : (joinEndpointDiagram B B ⊗ K).obj n)

/-- 概要：両端の和の図式を固定した分類図式の空間。
方針：関手空間の境界制限の指定頂点の fiber を取る。
規約：両端の図式 F と G は任意。
使われ方：表現空間の境界固定の図式射影の標的。 -/
def endpointPairDiagramSpace {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) :
    SSet.{u + 1} :=
  vertexFiber ((pre (prismEndpointPair B)).app SpaceInfinity)
    (functorVertex (joinEndpointDesc F G))

/-- 概要：固定境界の分類図式空間を coherent な変換空間へ写す。
方針：普遍図式の族を区間と底の積へ評価し二度 curry する。
規約：全高次の固定端点を保つ実際の単体集合の射。
使われ方：境界固定の表現の比較を変換空間へ移す。 -/
def endpointPairDiagramTransformationMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    endpointPairDiagramSpace F G ⟶ leftUnstraighteningTransformationSpace F G :=
  let q := vertexFiberι ((pre (prismEndpointPair B)).app SpaceInfinity)
    (functorVertex (joinEndpointDesc F G))
  let h := endpointPairDiagramFamily_endpoints F G q (vertexFiberι_comp _ _)
  coherentTransformationFamilyCurry F G ((α_ Δ[1] B _).inv ≫ uncurry q) h.1 h.2

/-- 概要：固定境界空間から作る変換の評価は元の普遍図式の評価。
方針：二つの curry と結合子の往復を消去する。
規約：全パラメーターで厳密な射の一致。
使われ方：実際の分類図式の回収。 -/
lemma endpointPairDiagramTransformationMap_prism {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    functorParameterizedPrism
      (intervalMappingUncurry (endpointPairDiagramTransformationMap F G)) =
      uncurry (vertexFiberι ((pre (prismEndpointPair B)).app SpaceInfinity)
        (functorVertex (joinEndpointDesc F G))) := by
  rw [endpointPairDiagramTransformationMap, coherentTransformationFamilyCurry_prism]
  simp only [Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories
