module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionLocalization

/-!
概要：準同型辺の公開集合から、同じ端点付き辺の閉零射の擬同型性を回収する。
方針：一次単体の等式から両端を回収し、元の閉射へ戻す。
規約：別の代表辺に置き換えない。
使われ方：実分解 augmentation のホモロジー自然同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarEdgeClosed_quasiIso_congr
    {x y x' y' : (dgModuleNerve R D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (dgModuleNerve R D)) x y)
    (e' : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (dgModuleNerve R D)) x' y')
    (h : e.edge = e'.edge) :
    moduleQuasiIso R D (DGNerve.HomotopyComparison.edgeClosed e) ↔
      moduleQuasiIso R D (DGNerve.HomotopyComparison.edgeClosed e') := by
  have hx : x = x' := e.src_eq.symm.trans
    ((congrArg (fun s => (dgModuleNerve R D).δ 1 s) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans
    ((congrArg (fun s => (dgModuleNerve R D).δ 0 s) h).trans e'.tgt_eq)
  subst x'
  subst y'
  have he : e = e' := SSet.Truncated.Edge.ext h
  rw [he]

lemma dgBarEdgeClosed_quasiIso_of_mem
    {x y : (dgModuleNerve R D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (dgModuleNerve R D)) x y)
    (he : e.edge ∈ dgModuleQuasiIsomorphismEdges R D) :
    moduleQuasiIso R D (DGNerve.HomotopyComparison.edgeClosed e) := by
  obtain ⟨M, N, f, hf, h⟩ := he
  apply (dgBarEdgeClosed_quasiIso_congr R D e (dgClosedEdge R (RightModule R D) f) h.symm).mpr
  simpa only [dgClosedEdge_closed] using hf

end SerrePositivity.InfinityCategories
