module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConePushout

/-! # dg 加群の nerve の全ての辺の cofiber

概要：実 cone の普遍性を任意の辺の cofiber の存在へ昇格する。
方針：全 Hom end の閉射と辺の同値を使い、入力辺を厳密に保つ四角形を作る。
規約：二切断の辺の代表を選び直して済ませない。使われ方：β3 の dg 加群模型の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉 dg 加群射の標準 cone はその実際の辺の cofiber を与える。 -/
def dgModuleCofiberSquare {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).toTruncated where
  toZeroTriangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle A D f
  bottom_edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_bottom A D f
  isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f

/-- dg 加群 nerve の辺は閉 dg 加群射の実際の辺として復元できる。 -/
lemma dgModuleEdge_edgeClosed {M N : _root_.SerrePositivity.DifferentialGraded.RightModule A D}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)).toTruncated = e :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)).symm_apply_apply e

/-- 全 Hom end を持つ dg 加群圏の nerve の全ての辺は実 cofiber を持つ。 -/
lemma dgModuleNerve_cofiber_exists {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare e) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  change Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (e : SSet.Truncated.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)))
  rw [← dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleCofiberSquare A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
