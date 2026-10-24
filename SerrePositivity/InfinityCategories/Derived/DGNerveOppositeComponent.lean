module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeHomotopy
/-!
概要：反転ホモトピーの実頂点辺と同じ閉 dg 射を回収する。
方針：同じ実 prism と反対比較を、一次単体と厳密切断で評価する。
規約：同じ全関手と閉射を保持する。使われ方：一般 RHom の標準写像空間判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

/-- 反対 nerve 比較の逆は、同じ反対対象の頂点を元の頂点へ戻す。 -/
lemma dgNerveOppositeIso_inv_vertex (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x : C) :
    (dgNerveOppositeIso R C).inv.app (Opposite.op ⦋0⦌) (Simplex.vertex (Opposite.op x)) =
      SSet.opObjEquiv.symm (Simplex.vertex x) := by
  rw [← dgNerveOppositeIso_hom_vertex R C x]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (Iso.hom_inv_id (dgNerveOppositeIso R C)) _) _

/-- 反転ホモトピーの実頂点辺は、元の頂点辺の符号付き実反転。 -/
lemma dgNerveOppositeHomotopy_vertex_edge (R : Type u) [CommRing R]
    (C E : Type v) [DGCategory R C] [DGCategory R E]
    (F G : DGFunctor R C E) (H : SSet.Homotopy (dgNerve.map F) (dgNerve.map G)) (x : C) :
    (simplicialHomotopyVertexEdge (dgNerveOppositeHomotopy R C E F G H)
      (Simplex.vertex (Opposite.op x))).edge =
      DGNerveOppositeData.opSimplex (simplicialHomotopyVertexEdge H (Simplex.vertex x)).edge := by
  change (dgNerveOppositeIso R E).hom.app (Opposite.op ⦋1⦌)
    ((SerrePositivity.InfinityCategories.homotopyOpposite H).h.app (Opposite.op ⦋1⦌)
      ((dgNerveOppositeIso R C).inv.app (Opposite.op ⦋1⦌)
        ((dgNerve R Cᵒᵖ).σ 0 (Simplex.vertex (Opposite.op x))), homotopyIntervalEdge.edge)) = _
  have hn := (dgNerveOppositeIso R C).inv.naturality_apply
    (SimplexCategory.σ (0 : Fin 1)).op (Simplex.vertex (Opposite.op x))
  change (dgNerveOppositeIso R C).inv.app (Opposite.op ⦋1⦌)
    ((dgNerve R Cᵒᵖ).σ 0 (Simplex.vertex (Opposite.op x))) = _ at hn
  rw [hn, dgNerveOppositeIso_inv_vertex]
  change (dgNerveOppositeIso R E).hom.app (Opposite.op ⦋1⦌)
    (simplicialHomotopyVertexEdge (SerrePositivity.InfinityCategories.homotopyOpposite H)
      (SSet.opObjEquiv.symm (Simplex.vertex x))).edge = _
  rw [kanHomotopyOpposite_vertex_edge]
  rfl

/-- 閉 dg 射の実辺の反転は、同じ閉射の反対から作る実辺。 -/
lemma opSimplex_dgClosedEdge (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] {x y : ClosedCategory R C} (f : x ⟶ y) :
    DGNerveOppositeData.opSimplex (dgClosedEdge R C f).edge =
      (dgClosedEdge R Cᵒᵖ ((forgetEnrichmentOppositeEquivalence (Complex R) C).inverse.map
        f.op)).edge := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    change DGNerveOppositeSigns.sign 2 • _ = _
    rw [DGNerveOppositeSigns.sign_two, one_smul]
    have hr : DGNerveOppositeIndex.reverse ({0, 1} : Finset (Fin 2)) = {0, 1} := by decide
    simp only [hr]
    rfl
end SerrePositivity.InfinityCategories
