module
public import SerrePositivity.KST.Fibration.KanPointComponentComposition
public import SerrePositivity.KST.Fibration.PointedSpaceHomPoint
public import SerrePositivity.KST.Fibration.PointedLeftResolutionVertices
public import SerrePositivity.KST.Fibration.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedReverseCompositionTransport
public import SerrePositivity.InfinityCategories.Stable.HomotopyOpposite
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso

/-! # Kan 写像の本質的全射性を、同じ点の射の全射性から回収する

実 pointed fiber の同型と、既存の全写像空間の同値による逆像を使う。
高次写像空間の充満忠実性を零次の主張で代用しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 標準の一点 Hom 同型で座標を揃えた、実 pointed fiber への既存比較。 -/
def kanPointFiberComparison (K : KanObject.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj K.obj).op ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex K) :=
  (SSet.opFunctor.mapIso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (pointKanObjectHomIso K))).inv ≫
      pointedReverseKanFiberComparison K

/-- 座標変更後も、同じ比較は全写像空間で充満忠実。 -/
theorem kanPointFiberComparison_isFullyFaithful (K : KanObject.{u}) :
    IsFullyFaithful (kanPointFiberComparison K) :=
  ((qCatEquivalenceOfIso (SSet.opFunctor.mapIso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (pointKanObjectHomIso K))).symm).isQCatEquivalence.comp
      (pointedReverseKanFiberComparison_isQCatEquivalence K)).isFullyFaithful

/-- 座標変更後の同じ比較は、元の指定した Kan 点の標準 pointed 表示を回収。 -/
theorem kanPointFiberComparison_vertex (K : KanObject.{u}) (v : K.obj _⦋0⦌) :
    (kanPointFiberComparison K).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (ULift.up v)) = (pointedSpaceFiberVertexEquiv K).symm v := by
  apply (pointedSpaceFiberVertexEquiv K).injective
  exact (pointedReverseKanFiberComparison_point K v).trans
    ((pointedSpaceFiberVertexEquiv K).apply_symm_apply v).symm

/-- 同じ Kan 値で点の射の類が一致すれば、元の二点は実際に同型。 -/
def kanVertexIsoOfPointHomEq (K : KanObject.{u}) {v w : K.obj _⦋0⦌}
    (h : cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv K).symm v) =
      cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv K).symm w)) :
    VertexIso (X := K.obj) v w := by
  let e := (kanPointFiberComparison_isFullyFaithful K).preimageVertexIso
    (eqToIso (congrArg HomotopyCategory.mk (kanPointFiberComparison_vertex K v)) ≪≫
      cosliceFiberVertexIsoOfHomEq h ≪≫
        (eqToIso (congrArg HomotopyCategory.mk (kanPointFiberComparison_vertex K w))).symm)
  let t := (homotopyOppositeEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).obj K.obj)).functor.mapIso e
  exact downVertexIso t.unop.symm

/-- 元の成分辺が全ての点の射を覆うなら、同じ Kan 写像は本質的全射。 -/
theorem kanMap_isEssentiallySurjective_of_point_surjective {K L : KanObject.{u}} (f : K ⟶ L)
    (e : SpaceInfinity.Edge (spaceInfinityVertex K) (spaceInfinityVertex L))
    (he : e.edge = (coherentNerveEdge f).edge)
    (hs : Function.Surjective (fun a : HomotopyCategory.mk pointSpaceVertex ⟶
        HomotopyCategory.mk (spaceInfinityVertex K) =>
      a ≫ Truncated.HomotopyCategory.homMk e.toTruncated)) : IsEssentiallySurjective f := by
  intro y
  obtain ⟨a, ha⟩ := hs (cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv L).symm y))
  let w := pointedSpaceFiberPointOfHom a
  let x := pointedSpaceFiberVertexEquiv K w
  have hx : (pointedSpaceFiberVertexEquiv K).symm x = w :=
    (pointedSpaceFiberVertexEquiv K).symm_apply_apply w
  refine ⟨x, ⟨kanVertexIsoOfPointHomEq L ?_⟩⟩
  have hp := (congrArg cosliceFiberPointHom hx).trans (pointedSpaceFiberPointOfHom_hom a)
  exact (kanPointHom_comp_of_edge f e he x).symm.trans
    ((congrArg (fun m => m ≫ Truncated.HomotopyCategory.homMk e.toTruncated) hp).trans ha)

end SerrePositivity.KST.Fibration
