module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingVertices
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningInvertibleTransformation
public import SerrePositivity.InfinityCategories.Core.PrecompositionHomotopy

/-!
概要：写像空間の unstraightening 比較の頂点が表す底上の射と、可逆な変換に対する同値性。
方針：一本の変換への作用との相対同型を全空間の関手同型へ写し、前合成同値の不変性を使う。
規約：可逆な変換の全空間の比較では底を quasicategory とする。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較と coherent な図式の同値の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像空間の比較射の任意の頂点の値を、実際の底上の射として取り出す。
方針：相対写像空間の頂点と底上の射の全単射を逆に使う。
規約：底を保つ可換性を部分型に保持する。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較が与える具体的な unstraightening の射。 -/
noncomputable def leftUnstraighteningMappingVertexMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    {f : leftUnstraightening F ⟶ leftUnstraightening G //
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F} :=
  (relativeFunctorVertexEquiv (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)).symm
    ((leftUnstraighteningMappingSpaceMap F G).app _ x)

/-- 概要：比較射の頂点から取り出した底上の射を相対頂点に戻すと、元の比較射の値になる。
方針：相対頂点と底上の射の全単射の往復を使う。
規約：可換性の証明も同時に保持する。
使われ方：Kerodon Corollary 5.6.0.6、比較射の値と具体的な底上の射の接続。 -/
lemma leftUnstraighteningMappingVertexMap_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningMappingVertexMap F G x).val (leftUnstraighteningMappingVertexMap F G x).property =
      (leftUnstraighteningMappingSpaceMap F G).app _ x :=
  (relativeFunctorVertexEquiv (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)).apply_symm_apply _

/-- 概要：写像空間の比較射に可逆な coherent な変換を入力すると、全空間の前合成同値である底上の射が得られる。
方針：個別の辺への作用との相対同型を全空間へ写し、前合成同値のホモトピー不変性を使う。
規約：比較射の空間全体で選択した持ち上げの値について述べる。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較と図式の同値の整合性。 -/
lemma leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) :
    IsPrecompositionEquivalence
      (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val := by
  let h := leftUnstraighteningMappingSpaceMap_edgeVertexIso F G e ≪≫
    (eqToIso (congrArg SSet.HomotopyCategory.mk
      (leftUnstraighteningMappingVertexMap_vertex F G (intervalMappingVertexOfEdge e)))).symm
  have h' : FunctorIso (leftUnstraighteningEdgeMap F G e).val
      (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val :=
    VertexIso.map h (vertexFiberι ((ihom (leftUnstraightening F)).map
      (leftUnstraighteningProjection G)) (functorVertex (leftUnstraighteningProjection F)))
  exact (isPrecompositionEquivalence_iff_of_homotopy h'.simplicialHomotopy
    (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge h') (FunctorIso.edge_isInvertible h'))).mp
        (leftUnstraighteningEdgeMap_isPrecompositionEquivalence_of_isInvertibleEdge F G e he)

/-- 概要：可逆な coherent な変換での写像空間の比較の値は quasicategory の同値を表す。
方針：底上の射の前合成同値から同値の逆データを得る。
規約：元の二つの全空間の quasicategory 性は底と left fibration 性から得る。
使われ方：Kerodon Corollary 5.6.0.6、coherent な同値を fibration の全空間の同値へ移す。 -/
lemma leftUnstraighteningMappingVertexMap_isQCatEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) :
    IsQCatEquivalence (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val :=
  (leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_isInvertibleEdge F G e he).isQCatEquivalence

end SerrePositivity.InfinityCategories
