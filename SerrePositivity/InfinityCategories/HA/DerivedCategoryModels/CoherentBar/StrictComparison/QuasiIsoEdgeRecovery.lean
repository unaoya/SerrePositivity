module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionLocalization

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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarEdgeClosed_quasiIso_congr
    {x y x' y' : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)) x y)
    (e' : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)) x' y')
    (h : e.edge = e'.edge) :
    moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e) ↔
      moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e') := by
  have hx : x = x' := e.src_eq.symm.trans
    ((congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D).δ 1 s) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans
    ((congrArg (fun s => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D).δ 0 s) h).trans e'.tgt_eq)
  subst x'
  subst y'
  have he : e = e' := SSet.Truncated.Edge.ext h
  rw [he]

lemma dgBarEdgeClosed_quasiIso_of_mem
    {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D)) x y)
    (he : e.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleQuasiIsomorphismEdges R D) :
    moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e) := by
  obtain ⟨M, N, f, hf, h⟩ := he
  apply (dgBarEdgeClosed_quasiIso_congr R D e (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R D) f) h.symm).mpr
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed] using hf

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
