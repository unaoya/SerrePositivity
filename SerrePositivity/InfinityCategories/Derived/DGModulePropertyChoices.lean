module
public import SerrePositivity.InfinityCategories.Derived.DGModulePropertySquares
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberExists
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects

/-! # 三角的対象条件で制限した加群 nerve の全辺の普遍四角形

概要：部分圏の入力辺を厳密に保つ双カルテジアンな cone/fiber 四角形を与える。
方針：辺の包含像を閉加群射へ戻し、標準四角形の全単体を制限する。
規約：頂点のラベルと元の辺を変更しない。使われ方：三角的条件の部分圏の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 条件付き加群の実辺の包含像を、元の対象を端点として読む。 -/
def dgModulePropertyAmbientEdge
    {M N : DGFullSubcategory (RightModule A D) (dgModuleHomotopyProperty A D P)}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) (dgModuleHomotopyProperty A D P))))
      (Simplex.vertex M) (Simplex.vertex N)) :
    SSet.Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D))
      (Simplex.vertex M.val) (Simplex.vertex N.val) := by
  let F := dgFullSubcategoryInclusion A (RightModule A D) (dgModuleHomotopyProperty A D P)
  let e' := e.map ((truncation 2).map (dgNerve.map F))
  exact { edge := e'.edge
          src_eq := e'.src_eq.trans (dgFunctorNerve_vertex F M)
          tgt_eq := e'.tgt_eq.trans (dgFunctorNerve_vertex F N) }

/-- 条件付き加群 nerve の全ての辺に双カルテジアンな cofiber がある。 -/
lemma dgModuleProperty_bicartesian_cofiber_exists
    {x y : (dgNerve A (DGFullSubcategory (RightModule A D)
      (dgModuleHomotopyProperty A D P))) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) (dgModuleHomotopyProperty A D P)))) x y) :
    ∃ s : CofiberSquare e, IsPullbackSquare s.square := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let a := dgModulePropertyAmbientEdge A D P e
  let f := edgeClosed a
  let F := dgModulePropertyConeSquare A D P f M.property N.property
  have he : (dgModuleEdge A D f).edge = a.edge :=
    congrArg SSet.Truncated.Edge.edge (dgModuleEdge_edgeClosed A D a)
  let s : CofiberSquare e := {
    square := F
    zero_corner := dgFullSquareLift_zero_corner A _ _ _ _
      (dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply dgFullSquareLift_edge A (RightModule A D)
        (dgModuleHomotopyProperty A D P) _ _ _ e
      rw [dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := dgModulePropertyConeSquare_isPushout A D P f M.property N.property }
  exact ⟨s, dgModulePropertyConeSquare_isPullback A D P f M.property N.property⟩

/-- 条件付き加群 nerve の全ての辺に双カルテジアンな fiber がある。 -/
lemma dgModuleProperty_bicartesian_fiber_exists
    {x y : (dgNerve A (DGFullSubcategory (RightModule A D)
      (dgModuleHomotopyProperty A D P))) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGFullSubcategory (RightModule A D) (dgModuleHomotopyProperty A D P)))) x y) :
    ∃ s : FiberSquare e, IsPushoutSquare s.square := by
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let a := dgModulePropertyAmbientEdge A D P e
  let f := edgeClosed a
  let F := dgModulePropertyFiberSquare A D P f M.property N.property
  have he : (dgModuleEdge A D f).edge = a.edge :=
    congrArg SSet.Truncated.Edge.edge (dgModuleEdge_edgeClosed A D a)
  let s : FiberSquare e := {
    square := F
    zero_corner := dgFullSquareLift_zero_corner A _ _ _ _
      (dgModuleFiberZeroTriangle A D f).zero_corner
    right_edge := by
      apply dgFullSquareLift_edge A (RightModule A D)
        (dgModuleHomotopyProperty A D P) _ _ _ e
      rw [dgModuleFiberSquare_right]
      exact congrArg SSet.yonedaEquiv.symm he
    isPullback := dgModulePropertyFiberSquare_isPullback A D P f M.property N.property }
  exact ⟨s, dgModulePropertyFiberSquare_isPushout A D P f M.property N.property⟩

end SerrePositivity.InfinityCategories
