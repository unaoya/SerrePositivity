module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFunctorEdge
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：coherent な図式間の可逆な変換は unstraightening 間の底上の同値を与える。
方針：同じ逆辺と二つの合成三角形を使い、変換の合成則と単位則から逆射のデータを作る。
規約：底は quasicategory。比較射は既に選択した底上の射そのもの。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式の同型類に対する復元の選択独立性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：可逆な coherent な変換に対応する unstraightening の射は quasicategory の同値。
方針：逆辺の二つの三角形の合成同型と恒等辺の単位同型を、全空間の関手同型へ写す。
規約：逆射も同じ底を保つ選択済みの射を使う。
使われ方：Kerodon Corollary 5.6.0.6、可逆な変換による全空間の底上の比較。 -/
lemma leftUnstraighteningEdgeMap_isQCatEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) : IsQCatEquivalence (leftUnstraighteningEdgeMap F G e).val := by
  obtain ⟨⟨i, σ, τ⟩⟩ := he.nonempty_inverse
  let f := (leftUnstraighteningEdgeMap F G e).val
  let g := (leftUnstraighteningEdgeMap G F i).val
  let hF := (leftUnstraighteningEdgeMap_compositionIso σ).symm ≪≫
    leftUnstraighteningEdgeMap_identityIso F
  let hG := (leftUnstraighteningEdgeMap_compositionIso τ).symm ≪≫
    leftUnstraighteningEdgeMap_identityIso G
  have hfg : FunctorIso (f ≫ g) (𝟙 (leftUnstraightening F)) :=
    VertexIso.map hF (vertexFiberι ((ihom (leftUnstraightening F)).map (leftUnstraighteningProjection F))
      (functorVertex (leftUnstraighteningProjection F)))
  have hgf : FunctorIso (g ≫ f) (𝟙 (leftUnstraightening G)) :=
    VertexIso.map hG (vertexFiberι ((ihom (leftUnstraightening G)).map (leftUnstraighteningProjection G))
      (functorVertex (leftUnstraighteningProjection G)))
  exact ⟨g, ⟨hfg⟩, ⟨hgf⟩⟩

/-- 概要：可逆な coherent な変換の unstraightening は任意の quasicategory への前合成同値。
方針：実際の逆射と可逆な二胞体を持つ同値から前合成の判定を使う。
規約：前合成同値は選択済みの底上の射の性質。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式の同型による相対写像空間の比較。 -/
lemma leftUnstraighteningEdgeMap_isPrecompositionEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) : IsPrecompositionEquivalence (leftUnstraighteningEdgeMap F G e).val :=
  (leftUnstraighteningEdgeMap_isQCatEquivalence_of_isInvertibleEdge F G e he).isPrecompositionEquivalence

/-- 概要：coherent な図式の関手同型は unstraightening の間の厳密な底上の前合成同値射を与える。
方針：関手同型を表す可逆な辺を選び、その unstraightening の射を使う。
規約：底 B は quasicategory。結論には底上の可換性を保持する。
使われ方：Kerodon Corollary 5.6.0.6、図式の同型類から fibration の同値類への整合性。 -/
lemma exists_leftUnstraighteningComparison_of_functorIso
    {B : SSet.{u + 1}} [Quasicategory B] {F G : B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    ∃ f : leftUnstraightening F ⟶ leftUnstraightening G,
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F ∧
      IsPrecompositionEquivalence f := by
  let e := FunctorIso.edge η
  exact ⟨(leftUnstraighteningEdgeMap F G e).val, (leftUnstraighteningEdgeMap F G e).property,
    leftUnstraighteningEdgeMap_isPrecompositionEquivalence_of_isInvertibleEdge F G e
      (FunctorIso.edge_isInvertible η)⟩

end SerrePositivity.InfinityCategories
