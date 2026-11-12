module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberExists

/-! # dg 加群の nerve の全ての辺の fiber

概要：shifted cone の実普遍性を任意の辺の fiber の存在へ昇格する。
方針：閉加群射と辺の同値を使い、入力辺を厳密に保つ引き戻し四角形を作る。
規約：h の fiber で代用しない。使われ方：β3 の dg 加群模型の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉 dg 加群射の shifted cone は実際の辺の fiber を与える。 -/
def dgModuleFiberSquareOfMorphism {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).toTruncated where
  toZeroTriangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberZeroTriangle A D f
  right_edge := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_right A D f
  isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPullback A D f

/-- 全 Hom end を持つ dg 加群圏の nerve の全ての辺は実 fiber を持つ。 -/
lemma dgModuleNerve_fiber_exists {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare e) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (e : SSet.Truncated.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D e]
  exact ⟨dgModuleFiberSquareOfMorphism A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
