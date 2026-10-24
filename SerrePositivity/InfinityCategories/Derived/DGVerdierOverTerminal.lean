module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverRefinement
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal

/-! # 実 Verdier over 圏の恒等分母は終対象

概要：実分母 over ∞ 圏の恒等辺の頂点を作り、その終対象性を証明する。
方針：恒等辺の分母条件と、全部分包含の充満忠実性による終対象の反映を使う。
規約：元の厳密分母圏の終対象性で済ませない。使われ方：商側実屋根の固定 Hom との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 実分母 over ∞ 圏の元の恒等分母の頂点。 -/
def dgVerdierOverIdentityVertex (P : Set D) (x : D) :
    (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  ⟨sliceIdentityCone (X := dgNerve A D) (Simplex.vertex x), by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    change (roofPointSliceVertexEdge _
      (sliceIdentityCone (X := dgNerve A D) (Simplex.vertex x))).edge ∈ _
    have he : (roofPointSliceVertexEdge _
        (sliceIdentityCone (X := dgNerve A D) (Simplex.vertex x))).edge =
        (Truncated.Edge.id (X := (truncation 2).obj (dgNerve A D)) (Simplex.vertex x)).edge := by
      change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
        SSet.const (Y := dgNerve A D) (Simplex.vertex x)) = _
      rw [SSet.comp_const]
      change (dgNerve A D).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op (Simplex.vertex x) =
        (dgNerve A D).map (SimplexCategory.σ (0 : Fin 1)).op (Simplex.vertex x)
      exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => (dgNerve A D).map α.op (Simplex.vertex x))
        (Subsingleton.elim _ _)
    rw [he]
    apply dgVerdierEdges_of_isInvertible
    let d := Truncated.Edge.id (X := (truncation 2).obj (dgNerve A D)) (Simplex.vertex x)
    have hd : IsInvertibleEdge (X := dgNerve A D) d := by
      change IsIso (Truncated.HomotopyCategory.homMk d)
      rw [Truncated.HomotopyCategory.homMk_id]
      infer_instance
    exact (isInvertibleEdge_congr (X := dgNerve A D)
      (e := edgeOfSimplex (X := dgNerve A D) d.edge) (f := d) rfl).mpr hd⟩

/-- 元の実恒等分母は、実 Verdier over ∞ 圏の終対象である。 -/
lemma dgVerdierOverIdentityVertex_isTerminal (P : Set D) (x : D) :
    IsTerminalVertex (dgVerdierOverIdentityVertex A D P x) := by
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι _
    (IsDGVerdierOverVertex A D P x)).reflects_isTerminalVertex
  exact SerrePositivity.InfinityCategories.F1B.sliceIdentityCone_isTerminalVertex (X := dgNerve A D) (Simplex.vertex x)

end SerrePositivity.InfinityCategories
