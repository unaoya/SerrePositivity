module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ClosedHomTransport
public import SerrePositivity.InfinityCategories.DGNerve.HomotopyCategory

/-!
概要：端点付き dg nerve 辺の閉射を元の一次単体の閉射と端点移送へ分解する。
方針：同じ閉零 cycle の異種等号で比較する。
規約：端点の指定を保持する。
使われ方：指定余錐の零次元係数と native な脚の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open DGNerve.HomotopyComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarEdgeClosed_recover {x y : (dgNerve R (RightModule R D)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (dgNerve R (RightModule R D))) x y) :
    edgeClosed e =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (edge_source_obj e).symm) ≫
        e.edge.edgeClosed 0 1 (by decide) ≫
          eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (edge_target_obj e)) := by
  apply (closedHomEquiv R (RightModule R D) _ _).injective
  apply Subtype.ext
  rw [edgeClosed_cycle]
  erw [dgBarClosedHom_transport R D (edge_source_obj e) (edge_target_obj e)
    (e.edge.edgeClosed 0 1 (by decide))]
  simp only [Simplex.edgeClosed, Equiv.apply_symm_apply]
  change (edgeCycle e).val = gradedHomTransport (edge_source_obj e) (edge_target_obj e) rfl
    (e.edge.edgeCycle 0 1 (by decide)).val
  exact eq_of_heq ((edgeCycle_val_heq e).trans
    (gradedHomTransport_heq (edge_source_obj e) (edge_target_obj e) rfl
      (e.edge.edgeCycle 0 1 (by decide)).val).symm)

lemma dgBarEdgeClosed_recover_transport
    {x y : (dgNerve R (RightModule R D)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (dgNerve R (RightModule R D))) x y)
    {S : DGNerve.Simplex R (RightModule R D) 1} (he : e.edge = S)
    {M N : RightModule R D} (hx : S.obj 0 = M) (hy : S.obj 1 = N)
    (hm : M = x.obj 0) (hn : N = y.obj 0) :
    eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hx.symm) ≫
        S.edgeClosed 0 1 (by decide) ≫
          eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hy) =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hm) ≫ edgeClosed e ≫
        eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hn.symm) := by
  subst S
  rw [dgBarEdgeClosed_recover]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]


end SerrePositivity.InfinityCategories
