module

public import SerrePositivity.KST.LocalizingInvariants.DiagramVertexPaths

/-!
概要：頂点の指定同型を、同じ射の類を持つ可逆 path の実頂点に表す。
方針：辺の表示の全射性と可逆辺の全部分複体を使う。
規約：始点・終点と指定同型の類を保持。使われ方：積同値による頂点の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.VertexIsoPath
variable {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌} (e : VertexIso x y)

def edge : X.Edge x y :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective x y e.hom))

lemma edge_hom : Truncated.HomotopyCategory.homMk (edge e).toTruncated = e.hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective x y e.hom)

lemma edge_invertible : IsInvertibleEdge (edge e).toTruncated := by
  change IsIso (Truncated.HomotopyCategory.homMk (edge e).toTruncated)
  rw [edge_hom]
  infer_instance

def path : (equivalencePath X) _⦋0⦌ :=
  ⟨functorVertex (SSet.yonedaEquiv.symm (edge e).edge), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, Functor.map_id_apply]
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply]
    exact (isInvertibleEdge_congr (e := (edge e).toTruncated)
      (f := edgeOfSimplex (edge e).edge) rfl).mp (edge_invertible e)⟩

lemma path_edge : intervalFunctorVertexEdge ((equivalencePathι X).app (Opposite.op ⦋0⦌)
    (path e)) = (edge e).edge := by
  change intervalFunctorVertexEdge (functorVertex (SSet.yonedaEquiv.symm (edge e).edge)) = _
  rw [intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply]

lemma path_source : (equivalencePathEndpoint X 0).app (Opposite.op ⦋0⦌) (path e) = x := by
  have h := (intervalFunctorVertexTypedEdge
    ((equivalencePathι X).app (Opposite.op ⦋0⦌) (path e))).src_eq
  change X.δ 1 (intervalFunctorVertexEdge
    ((equivalencePathι X).app (Opposite.op ⦋0⦌) (path e))) = _ at h
  rw [path_edge] at h
  exact h.symm.trans (edge e).src_eq

lemma path_target : (equivalencePathEndpoint X 1).app (Opposite.op ⦋0⦌) (path e) = y := by
  have h := (intervalFunctorVertexTypedEdge
    ((equivalencePathι X).app (Opposite.op ⦋0⦌) (path e))).tgt_eq
  change X.δ 0 (intervalFunctorVertexEdge
    ((equivalencePathι X).app (Opposite.op ⦋0⦌) (path e))) = _ at h
  rw [path_edge] at h
  exact h.symm.trans (edge e).tgt_eq

end SerrePositivity.KST.LocalizingInvariants.VertexIsoPath
