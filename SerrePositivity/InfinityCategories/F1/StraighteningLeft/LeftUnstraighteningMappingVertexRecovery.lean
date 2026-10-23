module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingInvertible

/-!
概要：写像空間の比較射の任意の頂点を、その頂点から回収した実際の変換に沿う作用と比較する。
方針：区間模型の頂点と実際の辺の全単射を用い、辺での比較と評価の計算を適用する。
規約：頂点の選択や代表への置き換えで同値類に落とさない。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射の頂点での検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像空間の比較射の頂点が表す底上の射は、普遍的な終点の族をその頂点で制限した射と一致する。
方針：相対頂点の二つの表示を比較し、関手頂点の単射性を使う。
規約：底上の射そのものの厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、任意の頂点での実際の unstraightening の射の評価。 -/
lemma leftUnstraighteningMappingVertexMap_eq_family {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    (leftUnstraighteningMappingVertexMap F G x).val =
      lift (𝟙 (leftUnstraightening F)) (SSet.const x) ≫ leftUnstraighteningMappingFamily F G := by
  have h := (leftUnstraighteningMappingVertexMap_vertex F G x).trans
    (leftUnstraighteningMappingSpaceMap_vertex F G x)
  exact functorVertex_injective (congrArg Subtype.val h)

/-- 概要：写像空間の比較の任意の頂点は、そこから回収した一本の変換の作用と底上の写像空間内で同型。
方針：頂点と辺の往復の等式に、辺での比較の同型を合成する。
規約：x は変換の空間の任意の頂点。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較の全頂点で個別の変換の作用を利用する。 -/
noncomputable def leftUnstraighteningMappingSpaceMap_vertexIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningEdgeMap F G (intervalMappingEdgeOfVertex x)).val
      (leftUnstraighteningEdgeMap F G (intervalMappingEdgeOfVertex x)).property)
      ((leftUnstraighteningMappingSpaceMap F G).app _ x) :=
  leftUnstraighteningMappingSpaceMap_edgeVertexIso F G (intervalMappingEdgeOfVertex x) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk
      (congrArg (fun z => (leftUnstraighteningMappingSpaceMap F G).app _ z)
        ((intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).apply_symm_apply x)))

/-- 概要：任意の頂点から回収した coherent な変換が可逆なら、比較射の値が表す底上の射は前合成同値。
方針：頂点と辺の往復で、可逆な辺に対する既存の保存の定理へ帰着する。
規約：底 B は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の任意の頂点での同値の検出。 -/
lemma leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_recoveredEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (hx : IsInvertibleEdge (intervalMappingEdgeOfVertex x)) :
    IsPrecompositionEquivalence (leftUnstraighteningMappingVertexMap F G x).val := by
  have h := leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_isInvertibleEdge
    F G (intervalMappingEdgeOfVertex x) hx
  have he : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex x) = x :=
    (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).apply_symm_apply x
  simpa only [he] using h

end SerrePositivity.InfinityCategories
