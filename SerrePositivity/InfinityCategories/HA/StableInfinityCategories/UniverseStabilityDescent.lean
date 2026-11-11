module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseUniversalSquares

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroObjects
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration

/-! # 安定性の宇宙降下

概要：ULift が安定なら元の quasicategory も安定である。
方針：実四角形の全写像の全単射で fiber/cofiber を戻し、零角と指定辺を照合する。
規約：安定性の三条件を直接降下する。使われ方：前三角 dg nerve の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet MonoidalCategory
open scoped _root_.Simplicial

/-- 零角を指定した三角形を実四角形として持ち上げる。 -/
def ZeroTriangle.ulift {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare t.square
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).1 t.zero_corner

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (ulift)


/-- 持ち上げた指定辺の Fiber 四角形を元の辺の実四角形へ降下する。 -/
def fiberSquareOfULift {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f := by
  let F := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareHomEquiv.{u, v} X).symm s.square
  have hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare F = s.square :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareHomEquiv.{u, v} X).apply_symm_apply s.square
  refine { square := F, zero_corner := ?_, right_edge := ?_, isPullback := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift.{u, v} _).2
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_vertex, hF]
    exact s.zero_corner
  · apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{u, v} X 1).injective
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_rightEdge, hF, s.right_edge]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge_yoneda f
  · apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPullbackSquare_iff_ulift.{u, v} F).2
    rw [hF]
    exact s.isPullback

/-- 持ち上げた指定辺の Cofiber 四角形を元の辺の実四角形へ降下する。 -/
def cofiberSquareOfULift {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f := by
  let F := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareHomEquiv.{u, v} X).symm s.square
  have hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare F = s.square :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareHomEquiv.{u, v} X).apply_symm_apply s.square
  refine { square := F, zero_corner := ?_, bottom_edge := ?_, isPushout := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift.{u, v} _).2
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_vertex, hF]
    exact s.zero_corner
  · apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSimplexHomEquiv.{u, v} X 1).injective
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_bottomEdge, hF, s.bottom_edge]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge_yoneda f
  · apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift.{u, v} F).2
    rw [hF]
    exact s.isPushout

/-- 安定性の零対象・全 fiber/cofiber・零角の判定は元の宇宙に降下する。 -/
theorem isStable_of_ulift {X : SSet.{u}} [Quasicategory X]
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{v, u}).obj X)) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X := by
  let := h
  refine {
    toHasZeroVertex := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasZeroVertex_iff_ulift.{u, v} X).2 inferInstance
    fiber_exists := ?_
    cofiber_exists := ?_
    fiber_iff_cofiber := ?_ }
  · intro x y f
    obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_exists
      (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f)
    exact ⟨fiberSquareOfULift f s⟩
  · intro x y f
    obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.cofiber_exists
      (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f)
    exact ⟨cofiberSquareOfULift f s⟩
  · intro t
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPullbackSquare_iff_ulift t.square).trans
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber (ZeroTriangle.ulift.{u, v} t)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift t.square).symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
