module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ClosedHomTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory

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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarEdgeClosed_recover {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))) x y) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e).symm) ≫
        e.edge.edgeClosed 0 1 (by decide) ≫
          eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e)) := by
  apply (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) _ _).injective
  apply Subtype.ext
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle]
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarClosedHom_transport R D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e)
    (e.edge.edgeClosed 0 1 (by decide))]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeClosed, Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e).val = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e) rfl
    (e.edge.edgeCycle 0 1 (by decide)).val
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq e).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e) rfl
      (e.edge.edgeCycle 0 1 (by decide)).val).symm)

lemma dgBarEdgeClosed_recover_transport
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))) x y)
    {S : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R D) 1} (he : e.edge = S)
    {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D} (hx : S.obj 0 = M) (hy : S.obj 1 = N)
    (hm : M = x.obj 0) (hn : N = y.obj 0) :
    eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hx.symm) ≫
        S.edgeClosed 0 1 (by decide) ≫
          eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hy) =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hm) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e ≫
        eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hn.symm) := by
  subst S
  rw [dgBarEdgeClosed_recover]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]


end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
