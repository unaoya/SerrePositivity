module

public import SerrePositivity.InfinityCategories.F1.CoherentKanInvertible
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingFiberTransport
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingInvertible
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：選択済みの unstraightening の写像空間比較は、変換の可逆性を保存・反映する。
方針：全空間の同値を fiber に制限し、普遍射影の transport から各評価の辺の可逆性を回収する。
規約：底は quasicategory。写像空間の比較の充満忠実性とは別の主張。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式の変換と底上の同値の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：辺を入力した写像空間比較の値が全空間の同値であることと、入力の変換が可逆であることは同値。
方針：必要条件は fiber の同値、transport の比較、評価ごとの可逆性の判定を合成する。
規約：比較射の頂点から実際に回収した底上の射を用いる。
使われ方：Kerodon Corollary 5.6.0.6、選択済みの unstraightening の作用の保守性。 -/
lemma leftUnstraighteningMappingEdge_isQCatEquivalence_iff_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    IsQCatEquivalence (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val ↔
      IsInvertibleEdge e := by
  constructor
  · intro he
    apply (isInvertibleEdge_iff_evaluateFunctorAt e.toTruncated).mpr
    intro b
    let f := leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)
    have hb := vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
      f.val f.property he.isPrecompositionEquivalence b
    have ha := (qCatEquivalenceOfIso (leftUnstraighteningFiberIso F b).symm).isQCatEquivalence
    have hc := (qCatEquivalenceOfIso (leftUnstraighteningFiberIso G b)).isQCatEquivalence
    have ht : IsQCatEquivalence (leftUnstraighteningPointedFiberMap F G f.val f.property b) :=
      ha.comp (hb.comp hc)
    have hi := leftUnstraighteningMappingVertex_pointedFiberTransportIso F G
      (intervalMappingVertexOfEdge e) b
    have he' : intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge e) = e :=
      (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).symm_apply_apply e
    rw [he'] at hi
    have heval := pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence
      (functorEdgeAt e b) (ht.ofFunctorIso hi)
    exact (isInvertibleEdge_congr (e := (functorEdgeAt e b).toTruncated)
      (f := e.toTruncated.map ((truncation 2).map (evaluateFunctorAt b))) rfl).mp heval
  · exact leftUnstraighteningMappingVertexMap_isQCatEquivalence_of_isInvertibleEdge F G e

/-- 概要：比較射の任意の頂点が回収する全空間の射は、その頂点が表す変換が可逆な場合に限り同値。
方針：写像空間の頂点と端点固定の辺の全単射で、辺に対する判定を移す。
規約：全変換の族に対して選択した比較射の実際の頂点で述べる。
使われ方：Kerodon Corollary 5.6.0.6、写像空間比較の全頂点における同値性の検出。 -/
lemma leftUnstraighteningMappingVertexMap_isQCatEquivalence_iff
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    IsQCatEquivalence (leftUnstraighteningMappingVertexMap F G x).val ↔
      IsInvertibleEdge (intervalMappingEdgeOfVertex x) := by
  have h := leftUnstraighteningMappingEdge_isQCatEquivalence_iff_isInvertibleEdge F G
    (intervalMappingEdgeOfVertex x)
  have hx : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex x) = x :=
    (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).apply_symm_apply x
  rw [hx] at h
  exact h

end SerrePositivity.InfinityCategories
