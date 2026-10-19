module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence

/-! # 指定対象を端点とする dg 関手の実辺の像

概要：実辺の像を像対象の標準頂点を端点として読み、その閉射を厳密に照合する。
方針：閉射からの辺の再構成と一次単体の関手性を使う。
規約：辺そのものを選び直さない。使われ方：商の指定三辺を保つ二単体の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable (F : DGFunctor A D E)

/-- 像対象の標準頂点を端点とする、指定実辺の dg 関手による像。 -/
def dgClosedMappedEdge {x y : ClosedCategory A D}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) x))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) y))) :
    Truncated.Edge (X := (truncation 2).obj (dgNerve A E))
      (Simplex.vertex (F.obj (ForgetEnrichment.to (Complex A) x)))
      (Simplex.vertex (F.obj (ForgetEnrichment.to (Complex A) y))) := by
  let a := e.map ((truncation 2).map (dgNerve.map F))
  exact { edge := a.edge
          src_eq := a.src_eq.trans (dgFunctorNerve_vertex F _)
          tgt_eq := a.tgt_eq.trans (dgFunctorNerve_vertex F _) }

/-- 像の実辺の閉射は、元の閉射の関手像そのもの。 -/
lemma dgClosedMappedEdge_closed {x y : ClosedCategory A D}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) x))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) y))) :
    edgeClosed (dgClosedMappedEdge A D E F e) = F.onClosed.map (edgeClosed e) := by
  have he : (dgClosedMappedEdge A D E F e).edge =
      (dgClosedEdge A E (F.onClosed.map (edgeClosed e))).edge := by
    change e.edge.map F = _
    exact (congrArg (fun a => a.edge.map F) (dgClosedEdge_edgeClosed A D e).symm).trans
      (dgClosedEdge_map A D F (edgeClosed e))
  have h := Truncated.Edge.ext he
  rw [h, dgClosedEdge_closed]

end SerrePositivity.InfinityCategories
