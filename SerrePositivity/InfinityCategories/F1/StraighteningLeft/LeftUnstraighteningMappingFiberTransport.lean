module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingVertexRecovery
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom

/-!
概要：写像空間比較射の任意の頂点での fiber の作用と標準 transport の比較。
方針：比較射の頂点を個別の辺への作用と相対写像空間内で比較し、fiber へ制限する。
規約：入力は変換の空間の任意の頂点であり、可逆性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、選択済みの比較射の値での作用を transport と同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像空間比較射の任意の頂点が fiber に誘導する射は、評価した辺の標準 transport と関手同型。
方針：相対頂点の比較を fiber 間の内部 Hom へ写し、fiber 同型で移送して transport の比較に合成する。
規約：図式の底 B は任意で、比較射から回収した実際の底上の射を用いる。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射と空間値の作用の接続の頂点部分。 -/
noncomputable def leftUnstraighteningMappingVertex_pointedFiberTransportIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌) :
    FunctorIso
      (leftUnstraighteningPointedFiberMap F G (leftUnstraighteningMappingVertexMap F G x).val
        (leftUnstraighteningMappingVertexMap F G x).property b)
      (edgeTransport pointedSpaceProjection (functorEdgeAt (intervalMappingEdgeOfVertex x) b)) := by
  have h := leftUnstraighteningMappingSpaceMap_vertexIso F G x
  rw [← leftUnstraighteningMappingVertexMap_vertex] at h
  have h' := VertexIso.map h (relativeFunctorFiberHom
    (leftUnstraighteningProjection F) (leftUnstraighteningProjection G) b)
  rw [relativeFunctorFiberHom_vertex, relativeFunctorFiberHom_vertex] at h'
  have h'' := FunctorIso.precomp
    (FunctorIso.postcomp h' (leftUnstraighteningFiberIso G b).hom)
    (leftUnstraighteningFiberIso F b).inv
  exact h''.symm ≪≫ leftUnstraighteningEdgeMap_pointedFiberTransportIso F G
    (intervalMappingEdgeOfVertex x) b

end SerrePositivity.InfinityCategories
