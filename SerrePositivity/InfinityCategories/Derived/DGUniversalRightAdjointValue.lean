module
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCommaCounitComponent
/-!
概要：厳密切断の実普遍余単位と右随伴候補の各値を回収する。
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

/-- 同じ厳密切断が選ぶ普遍余単位の実対象。 -/
def dgUniversalRightAdjointObject
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) (y : E) :
    DGUniversalComma R C E F := Simplex.vertexEquiv
      ((dgUniversalCommaNerveEquivalence R C E F h).inv.app (Opposite.op ⦋0⦌)
        (Simplex.vertex y))

/-- 厳密切断が選ぶ普遍余単位の標的は、元の同じ対象。 -/
lemma dgUniversalRightAdjointObject_target
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) (y : E) :
    (dgUniversalRightAdjointObject R C E F h y).label.target = y := by
  have he := congrArg (fun f ↦ Simplex.vertexEquiv
    (f.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgUniversalCommaNerveEquivalence_inv_hom R C E F h)
  exact he

/-- 右随伴候補の実余単位の頂点辺は、同じ厳密切断で選ぶ閉射。 -/
lemma dgUniversalRightAdjointCounitHomotopy_vertex_edge
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
    (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y)) (y : E) :
    (simplicialHomotopyVertexEdge (dgUniversalRightAdjointCounitHomotopy R C E F h)
      (Simplex.vertex y)).edge =
      (dgClosedEdge R E
        (dgUniversalRightAdjointObject R C E F h y).label.universal.counit).edge := by
  let s := (dgUniversalCommaNerveEquivalence R C E F h).inv
  have hn := s.naturality_apply (SimplexCategory.σ (0 : Fin 1)).op (Simplex.vertex y)
  change (dgUniversalCommaCounitHomotopy R C E F).h.app (Opposite.op ⦋1⦌)
    (s.app (Opposite.op ⦋1⦌) ((dgNerve R E).σ 0 (Simplex.vertex y)),
      homotopyIntervalEdge.edge) = _
  change s.app (Opposite.op ⦋1⦌) ((dgNerve R E).σ 0 (Simplex.vertex y)) = _ at hn
  rw [hn]
  have hv : s.app (Opposite.op ⦋0⦌) (Simplex.vertex y) =
      Simplex.vertex (dgUniversalRightAdjointObject R C E F h y) := by
    apply Simplex.vertexEquiv.injective
    rfl
  rw [hv]
  exact dgUniversalCommaCounitHomotopy_vertex_edge R C E F _
end SerrePositivity.InfinityCategories
