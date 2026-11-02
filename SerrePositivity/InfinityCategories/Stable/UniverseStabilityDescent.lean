module

public import SerrePositivity.InfinityCategories.Core.UniverseZeroObjects
public import SerrePositivity.InfinityCategories.Core.UniverseSquareHom
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration

/-! # 安定性の宇宙降下

概要：ULift が安定なら元の quasicategory も安定である。
方針：実四角形の全写像の全単射で fiber/cofiber を戻し、零角と指定辺を照合する。
規約：安定性の三条件を直接降下する。使われ方：前三角 dg nerve の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial

/-- 零角を指定した三角形を実四角形として持ち上げる。 -/
def ZeroTriangle.ulift {X : SSet.{u}} (t : ZeroTriangle X) :
    ZeroTriangle ((SSet.uliftFunctor.{v, u}).obj X) where
  square := uliftSquare t.square
  zero_corner := by
    rw [uliftSquare_vertex]
    exact (isZeroVertex_iff_ulift _).1 t.zero_corner

/-- 持ち上げた指定辺の Fiber 四角形を元の辺の実四角形へ降下する。 -/
def fiberSquareOfULift {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (s : FiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f)) :
    FiberSquare f := by
  let F := (uliftSquareHomEquiv.{u, v} X).symm s.square
  have hF : uliftSquare F = s.square :=
    (uliftSquareHomEquiv.{u, v} X).apply_symm_apply s.square
  refine { square := F, zero_corner := ?_, right_edge := ?_, isPullback := ?_ }
  · apply (isZeroVertex_iff_ulift.{u, v} _).2
    rw [← uliftSquare_vertex, hF]
    exact s.zero_corner
  · apply (uliftSimplexHomEquiv.{u, v} X 1).injective
    rw [← uliftSquare_rightEdge, hF, s.right_edge]
    exact uliftEdge_yoneda f
  · apply (isPullbackSquare_iff_ulift.{u, v} F).2
    rw [hF]
    exact s.isPullback

/-- 持ち上げた指定辺の Cofiber 四角形を元の辺の実四角形へ降下する。 -/
def cofiberSquareOfULift {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (s : CofiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f)) :
    CofiberSquare f := by
  let F := (uliftSquareHomEquiv.{u, v} X).symm s.square
  have hF : uliftSquare F = s.square :=
    (uliftSquareHomEquiv.{u, v} X).apply_symm_apply s.square
  refine { square := F, zero_corner := ?_, bottom_edge := ?_, isPushout := ?_ }
  · apply (isZeroVertex_iff_ulift.{u, v} _).2
    rw [← uliftSquare_vertex, hF]
    exact s.zero_corner
  · apply (uliftSimplexHomEquiv.{u, v} X 1).injective
    rw [← uliftSquare_bottomEdge, hF, s.bottom_edge]
    exact uliftEdge_yoneda f
  · apply (isPushoutSquare_iff_ulift.{u, v} F).2
    rw [hF]
    exact s.isPushout

/-- 安定性の零対象・全 fiber/cofiber・零角の判定は元の宇宙に降下する。 -/
theorem isStable_of_ulift {X : SSet.{u}} [Quasicategory X]
    (h : IsStable ((SSet.uliftFunctor.{v, u}).obj X)) : IsStable X := by
  let := h
  refine {
    toHasZeroVertex := (hasZeroVertex_iff_ulift.{u, v} X).2 inferInstance
    fiber_exists := ?_
    cofiber_exists := ?_
    fiber_iff_cofiber := ?_ }
  · intro x y f
    obtain ⟨s⟩ := IsStable.fiber_exists
      (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f)
    exact ⟨fiberSquareOfULift f s⟩
  · intro x y f
    obtain ⟨s⟩ := IsStable.cofiber_exists
      (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f)
    exact ⟨cofiberSquareOfULift f s⟩
  · intro t
    exact (isPullbackSquare_iff_ulift t.square).trans
      ((IsStable.fiber_iff_cofiber (ZeroTriangle.ulift.{u, v} t)).trans
        (isPushoutSquare_iff_ulift t.square).symm)

end SerrePositivity.InfinityCategories
