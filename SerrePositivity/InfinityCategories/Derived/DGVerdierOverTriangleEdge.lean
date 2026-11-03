module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTriangleInverse
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOver
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexEdgeLift

/-! # 指定合成三角形による実 Verdier over の辺

概要：元の合成三角形を、元の二つの実分母頂点を結ぶ実 over 辺へ上げる。
方針：点上の slice の辺の逆構成を、両端が分母である全部分複体へ持ち上げる。
規約：辺の始域射影を厳密に保持。使われ方：実分母の有限共通始錐。
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

omit [Small.{u} D] in
/-- 実分母を結ぶ合成三角形は、指定始域辺を保つ実 over の辺を与える。 -/
lemma dgVerdierOver_exists_edgeOfCompStruct (P : Set D) (x : D)
    (s t : (dgVerdierOver A D P x : SSet) _⦋0⦌)
    (r : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      ((dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) s)
      ((dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) t))
    (h : Truncated.Edge.CompStruct r
      (roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := dgNerve A D)).symm
        (Simplex.vertex x)) t.val)
      (roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := dgNerve A D)).symm
        (Simplex.vertex x)) s.val)) :
    ∃ e : Truncated.Edge (X := (truncation 2).obj
      (dgVerdierOver A D P x : SSet.{max u v})) s t,
      (dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) e.edge = r.edge := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let e := roofPointSliceEdgeOfCompStruct a s.val t.val r h
  obtain ⟨e', he'⟩ := exists_fullSubcomplexEdgeLift (IsDGVerdierOverVertex A D P x) s t e
  refine ⟨e', ?_⟩
  have hp := congrArg (fun k =>
    (sliceOverProjection a).app (Opposite.op ⦋1⦌) k.edge) he'
  exact hp.trans (roofPointSliceSimplexOfCompStruct_projection a s.val t.val r h)

end SerrePositivity.InfinityCategories
