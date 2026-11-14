module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTriangleInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOver
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FullSubcomplexEdgeLift

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 実分母を結ぶ合成三角形は、指定始域辺を保つ実 over の辺を与える。 -/
lemma dgVerdierOver_exists_edgeOfCompStruct (P : Set D) (x : D)
    (s t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌)
    (r : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) s)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) t))
    (h : Truncated.Edge.CompStruct r
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) t.val)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) s.val)) :
    ∃ e : Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) s t,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌) e.edge = r.edge := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeOfCompStruct a s.val t.val r h
  obtain ⟨e', he'⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fullSubcomplexEdgeLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x) s t e
  refine ⟨e', ?_⟩
  have hp := congrArg (fun k =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a).app (Opposite.op ⦋1⦌) k.edge) he'
  exact hp.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplexOfCompStruct_projection a s.val t.val r h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
