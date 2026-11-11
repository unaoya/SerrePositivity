module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedPropertySquares
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberExists
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroObjects

/-!
概要：閉性を満たす全 dg 加群部分圏の実双カルテジアンな選択。
方針：指定した実辺を閉射へ戻し、周囲の同じ四角形を部分圏へ制限する。
規約：replete 性を要求しない。使われ方：β5 の全半自由模型の安定性比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : RightModule A D → Prop) (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedProperty A D P)

/-- 条件付き加群の実辺の包含像を、元の対象を端点として読む。 -/
def dgClosedModuleAmbientEdge
    {M N : _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (P)}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) (P))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N.val) := by
  let F := _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (P)
  let e' := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))
  exact { edge := e'.edge
          src_eq := e'.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F M)
          tgt_eq := e'.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F N) }

include hP
/-- 条件付き加群 nerve の全ての辺に双カルテジアンな cofiber がある。 -/
lemma dgClosedModule_bicartesian_cofiber_exists
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D)
      (P))) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) (P)))) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let a := dgClosedModuleAmbientEdge A D P e
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed a
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare A D P hP f M.property N.property
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge = a.edge :=
    congrArg SSet.Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D a)
  let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e := {
    square := F
    zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_zero_corner A _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_edge A (RightModule A D)
        (P) _ _ _ e
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare_isPushout A D P hP f M.property N.property }
  exact ⟨s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleConeSquare_isPullback A D P hP f M.property N.property⟩

/-- 条件付き加群 nerve の全ての辺に双カルテジアンな fiber がある。 -/
lemma dgClosedModule_bicartesian_fiber_exists
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D)
      (P))) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) (P)))) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let a := dgClosedModuleAmbientEdge A D P e
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed a
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleFiberSquare A D P hP f M.property N.property
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge = a.edge :=
    congrArg SSet.Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D a)
  let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare e := {
    square := F
    zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_zero_corner A _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberZeroTriangle A D f).zero_corner
    right_edge := by
      apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_edge A (RightModule A D)
        (P) _ _ _ e
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_right]
      exact congrArg SSet.yonedaEquiv.symm he
    isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleFiberSquare_isPullback A D P hP f M.property N.property }
  exact ⟨s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleFiberSquare_isPushout A D P hP f M.property N.property⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
