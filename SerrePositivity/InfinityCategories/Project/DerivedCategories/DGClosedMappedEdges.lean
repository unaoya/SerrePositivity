module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEquivalence

/-! # 指定対象を端点とする dg 関手の実辺の像

概要：実辺の像を像対象の標準頂点を端点として読み、その閉射を厳密に照合する。
方針：閉射からの辺の再構成と一次単体の関手性を使う。
規約：辺そのものを選び直さない。使われ方：商の指定三辺を保つ二単体の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 像対象の標準頂点を端点とする、指定実辺の dg 関手による像。 -/
def dgClosedMappedEdge {x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) y))) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj (ForgetEnrichment.to (Complex A) x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj (ForgetEnrichment.to (Complex A) y))) := by
  let a := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))
  exact { edge := a.edge
          src_eq := a.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F _)
          tgt_eq := a.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F _) }

/-- 像の実辺の閉射は、元の閉射の関手像そのもの。 -/
lemma dgClosedMappedEdge_closed {x y : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) y))) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (dgClosedMappedEdge A D E F e) = F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e) := by
  have he : (dgClosedMappedEdge A D E F e).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A E (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))).edge := by
    change e.edge.map F = _
    exact (congrArg (fun a => a.edge.map F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_edgeClosed A D e).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map A D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))
  have h := Truncated.Edge.ext he
  rw [h, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
