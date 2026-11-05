module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom
public import SerrePositivity.InfinityCategories.F1.Straightening.SmallUnstraighteningFunctorHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingFiberTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberFamily

/-! # 全変換空間の実 pointed-fiber 作用を、同じ二胞体の成分との合成として読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 関手辺の実頂点評価の類は、同じ関手辺の二胞体を評価した成分。 -/
theorem functorHomEvaluate_edge_hom {D X : SSet.{u}} {F G : D ⟶ X}
    (e : SSet.Edge (functorVertex F) (functorVertex G)) (b : D _⦋0⦌) :
    functorHomEvaluate (Truncated.HomotopyCategory.homMk e.toTruncated) b =
      Truncated.HomotopyCategory.homMk (functorEdgeAt e b).toTruncated := by
  exact homMk_transport (evaluateFunctorAt_functorVertex b F)
    (evaluateFunctorAt_functorVertex b G)
    (e.map (evaluateFunctorAt b)).toTruncated (functorEdgeAt e b).toTruncated rfl

/-- 全写像空間の比較の頂点での fiber 作用は、同じ頂点から回収した底上の写像の作用。 -/
theorem pointedTransformationFiberHom_vertex {D : SSet.{u + 1}}
    (F G : D ⟶ SpaceInfinity.{u})
    (s : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : D _⦋0⦌) :
    (leftUnstraighteningMappingFiberHom F G b).app (Opposite.op ⦋0⦌) s =
      functorVertex (leftUnstraighteningPointedFiberMap F G
        (leftUnstraighteningMappingVertexMap F G s).val
        (leftUnstraighteningMappingVertexMap F G s).property b) := by
  change ((ihom (vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b))).map
    (leftUnstraighteningFiberIso G b).hom).app (Opposite.op ⦋0⦌)
      (((pre (leftUnstraighteningFiberIso F b).inv).app _).app (Opposite.op ⦋0⦌)
        ((relativeFunctorFiberHom (leftUnstraighteningProjection F)
          (leftUnstraighteningProjection G) b).app (Opposite.op ⦋0⦌)
            ((leftUnstraighteningMappingSpaceMap F G).app (Opposite.op ⦋0⦌) s))) = _
  rw [← leftUnstraighteningMappingVertexMap_vertex, relativeFunctorFiberHom_vertex]
  rfl

/-- 全変換空間の実作用は、元の点の射と同じ変換の実評価辺との合成を表す。 -/
theorem pointedTransformationPointHom {D : SSet.{u + 1}}
    (F G : D ⟶ SpaceInfinity.{u})
    (s : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : D _⦋0⦌)
    (v : (vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom v ≫ Truncated.HomotopyCategory.homMk
      (functorEdgeAt (intervalMappingEdgeOfVertex s) b).toTruncated =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
        ((leftUnstraighteningMappingFiberHom F G b ≫ evaluateFunctorAt v).app
          (Opposite.op ⦋0⦌) s) := by
  let T := leftUnstraighteningPointedFiberMap F G
    (leftUnstraighteningMappingVertexMap F G s).val
    (leftUnstraighteningMappingVertexMap F G s).property b
  let e := functorEdgeAt (intervalMappingEdgeOfVertex s) b
  have hi := VertexIso.map
    (leftUnstraighteningMappingVertex_pointedFiberTransportIso F G s b) (evaluateFunctorAt v)
  simp only [evaluateFunctorAt_functorVertex] at hi
  have hp := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom_eq_of_vertexIso hi
  have hc := _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceTransportPointHom e (edgeTransport pointedSpaceProjection e)
    (edgeTransport_isTransport pointedSpaceProjection e) v
  have hv : (leftUnstraighteningMappingFiberHom F G b ≫ evaluateFunctorAt v).app
      (Opposite.op ⦋0⦌) s = T.app (Opposite.op ⦋0⦌) v := by
    change (evaluateFunctorAt v).app (Opposite.op ⦋0⦌)
      ((leftUnstraighteningMappingFiberHom F G b).app (Opposite.op ⦋0⦌) s) = _
    rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedTransformationFiberHom_vertex, evaluateFunctorAt_functorVertex]
  exact hc.trans (hp.symm.trans (congrArg _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom hv.symm))

/-- 指定した元の二胞体を実作用で評価しても、同じ点の射との合成の類を保持する。 -/
theorem pointedFunctorHomPointHom {B : SSet.{u}}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : FunctorHom F G) (b : B _⦋0⦌)
    (v : (vertexFiber pointedSpaceProjection
      (F.app (Opposite.op ⦋0⦌) (ULift.up b))) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom v ≫ functorHomEvaluate a (ULift.up b) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom
        ((leftUnstraighteningMappingFiberHom F G (ULift.up b) ≫ evaluateFunctorAt v).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a)) := by
  have hc := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedTransformationPointHom F G (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a)
    (ULift.up b) v
  have hs : intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomParameter a) =
      _root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge a :=
    (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).symm_apply_apply _
  have he := (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorHomEvaluate_edge_hom (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge a) (ULift.up b)).symm
  have hclass := congrArg (fun m => functorHomEvaluate m (ULift.up b))
    (_root_.SerrePositivity.InfinityCategories.F1.Straightening.smallUnstraighteningHomEdge_hom a)
  rw [hs] at hc
  rw [he.trans hclass] at hc
  exact hc

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorHomEvaluate_edge_hom := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorHomEvaluate_edge_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedFunctorHomPointHom := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFunctorHomPointHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedTransformationFiberHom_vertex := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedTransformationFiberHom_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedTransformationPointHom := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedTransformationPointHom
