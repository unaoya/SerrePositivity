module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxFixedInputFamily
public import SerrePositivity.InfinityCategories.F2.LaxPullbackVertexEquiv
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence

/-! 端点固定の区間 Hom の頂点同型を、同じ二入力を持つ lax pullback の頂点同型へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
  (a : A _⦋0⦌) (b : B _⦋0⦌)

def dgGluingLaxFixedInputVertex (e : C.Edge (p.app _ a) (q.app _ b)) :
    (F2.laxPullback p q) _⦋0⦌ :=
  F2.laxPullbackVertexOfData p q ⟨a, b, e.edge, e.src_eq, e.tgt_eq⟩

lemma dgGluingLaxFixedInputVertex_exists (z : (F2.laxPullback p q) _⦋0⦌) :
    ∃ (a : A _⦋0⦌) (b : B _⦋0⦌) (e : C.Edge (p.app _ a) (q.app _ b)),
      dgGluingLaxFixedInputVertex p q a b e = z := by
  let d := F2.laxPullbackVertexData p q z
  exact ⟨d.left, d.right, ⟨d.arrow, d.source, d.target⟩,
    F2.laxPullbackVertexOfData_data p q z⟩

lemma dgGluingLaxFixedInputFamily_vertex (e : C.Edge (p.app _ a) (q.app _ b)) :
    (dgGluingLaxFixedInputFamily p q a b).app (Opposite.op ⦋0⦌)
        (intervalMappingVertexOfEdge e) = dgGluingLaxFixedInputVertex p q a b e := by
  apply (F2.laxPullbackVertexEquiv p q).injective
  change F2.laxPullbackVertexData p q _ =
    F2.laxPullbackVertexData p q (F2.laxPullbackVertexOfData p q _)
  rw [F2.laxPullbackVertexData_ofData]
  apply F2.LaxPullbackVertexData.ext
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingLaxFixedInputFamily_left p q a b) (Opposite.op ⦋0⦌))
        (intervalMappingVertexOfEdge e)
    change (F2.laxPullbackFst p q).app _
      ((dgGluingLaxFixedInputFamily p q a b).app _ (intervalMappingVertexOfEdge e)) = _
    change (F2.laxPullbackFst p q).app (Opposite.op ⦋0⦌)
      ((dgGluingLaxFixedInputFamily p q a b).app (Opposite.op ⦋0⦌)
        (intervalMappingVertexOfEdge e)) = PinchedHom.constant a 0 at h
    simpa only [pinchedConstant_zero] using h
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingLaxFixedInputFamily_right p q a b) (Opposite.op ⦋0⦌))
        (intervalMappingVertexOfEdge e)
    change (F2.laxPullbackSnd p q).app _
      ((dgGluingLaxFixedInputFamily p q a b).app _ (intervalMappingVertexOfEdge e)) = _
    change (F2.laxPullbackSnd p q).app (Opposite.op ⦋0⦌)
      ((dgGluingLaxFixedInputFamily p q a b).app (Opposite.op ⦋0⦌)
        (intervalMappingVertexOfEdge e)) = PinchedHom.constant b 0 at h
    simpa only [pinchedConstant_zero] using h
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (dgGluingLaxFixedInputFamily_arrow p q a b) (Opposite.op ⦋0⦌))
        (intervalMappingVertexOfEdge e)
    change (F2.laxPullbackArrow p q).app (Opposite.op ⦋0⦌)
      ((dgGluingLaxFixedInputFamily p q a b).app (Opposite.op ⦋0⦌)
        (intervalMappingVertexOfEdge e)) =
      (dgGluingIntervalArrowFamily (p.app _ a) (q.app _ b)).app (Opposite.op ⦋0⦌)
        (intervalMappingVertexOfEdge e) at h
    change intervalFunctorVertexEdge
      ((F2.laxPullbackArrow p q).app _
        ((dgGluingLaxFixedInputFamily p q a b).app _ (intervalMappingVertexOfEdge e))) = _
    rw [h, dgGluingIntervalArrowFamily_eq]
    exact (F2.intervalFunctorVertexEdgeEquiv C).apply_symm_apply e.edge

def dgGluingLaxFixedInputVertexIso
    {e f : C.Edge (p.app _ a) (q.app _ b)}
    (h : VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f)) :
    VertexIso (dgGluingLaxFixedInputVertex p q a b e) (dgGluingLaxFixedInputVertex p q a b f) := by
  have hi := VertexIso.map h (dgGluingLaxFixedInputFamily p q a b)
  simpa only [dgGluingLaxFixedInputFamily_vertex] using hi

end SerrePositivity.InfinityCategories
