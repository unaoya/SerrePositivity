module
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedPropertySquares
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberExists
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects

/-!
概要：閉性を満たす全 dg 加群部分圏の実双カルテジアンな選択。
方針：指定した実辺を閉射へ戻し、周囲の同じ四角形を部分圏へ制限する。
規約：replete 性を要求しない。使われ方：β5 の全半自由模型の安定性比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : RightModule A D → Prop) (hP : DGModuleClosedProperty A D P)

/-- 条件付き加群の実辺の包含像を、元の対象を端点として読む。 -/
def dgClosedModuleAmbientEdge
    {M N : DGFullSubcategory (RightModule A D) (P)}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) (P))))
      (Simplex.vertex M) (Simplex.vertex N)) :
    SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D))
      (Simplex.vertex M.val) (Simplex.vertex N.val) := by
  let F := dgFullSubcategoryInclusion A (RightModule A D) (P)
  let e' := e.map ((truncation 2).map (dgNerve.map F))
  exact { edge := e'.edge
          src_eq := e'.src_eq.trans (dgFunctorNerve_vertex F M)
          tgt_eq := e'.tgt_eq.trans (dgFunctorNerve_vertex F N) }

include hP
/-- 条件付き加群 nerve の全ての辺に双カルテジアンな cofiber がある。 -/
lemma dgClosedModule_bicartesian_cofiber_exists
    {x y : (dgNerve A (DGFullSubcategory (RightModule A D)
      (P))) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) (P)))) x y) :
    ∃ s : CofiberSquare e, IsPullbackSquare s.square := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let a := dgClosedModuleAmbientEdge A D P e
  let f := edgeClosed a
  let F := dgClosedModuleConeSquare A D P hP f M.property N.property
  have he : (dgModuleEdge A D f).edge = a.edge :=
    congrArg SSet.Truncated.Edge.edge (dgModuleEdge_edgeClosed A D a)
  let s : CofiberSquare e := {
    square := F
    zero_corner := dgFullSquareLift_zero_corner A _ _ _ _
      (dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply dgFullSquareLift_edge A (RightModule A D)
        (P) _ _ _ e
      rw [dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := dgClosedModuleConeSquare_isPushout A D P hP f M.property N.property }
  exact ⟨s, dgClosedModuleConeSquare_isPullback A D P hP f M.property N.property⟩

/-- 条件付き加群 nerve の全ての辺に双カルテジアンな fiber がある。 -/
lemma dgClosedModule_bicartesian_fiber_exists
    {x y : (dgNerve A (DGFullSubcategory (RightModule A D)
      (P))) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) (P)))) x y) :
    ∃ s : FiberSquare e, IsPushoutSquare s.square := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let a := dgClosedModuleAmbientEdge A D P e
  let f := edgeClosed a
  let F := dgClosedModuleFiberSquare A D P hP f M.property N.property
  have he : (dgModuleEdge A D f).edge = a.edge :=
    congrArg SSet.Truncated.Edge.edge (dgModuleEdge_edgeClosed A D a)
  let s : FiberSquare e := {
    square := F
    zero_corner := dgFullSquareLift_zero_corner A _ _ _ _
      (dgModuleFiberZeroTriangle A D f).zero_corner
    right_edge := by
      apply dgFullSquareLift_edge A (RightModule A D)
        (P) _ _ _ e
      rw [dgModuleFiberSquare_right]
      exact congrArg SSet.yonedaEquiv.symm he
    isPullback := dgClosedModuleFiberSquare_isPullback A D P hP f M.property N.property }
  exact ⟨s, dgClosedModuleFiberSquare_isPushout A D P hP f M.property N.property⟩

end SerrePositivity.InfinityCategories
