module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseBoundaryHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseUniversalSquares
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroObjects
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseZeroTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-!
概要：元の安定 ∞ 圏の単体集合の宇宙持ち上げは安定。
方針：元の指定辺の実 fiber/cofiber 四角形を持ち上げ、任意の零角四角形の判定を降ろす。
規約：全四角形・指定辺・零角の実写像を保持し、新しい安定性を仮定しない。
使われ方：元の C の ULift を始域とする idemYoneda への HA 1.1.3.7 の適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent

/-- 元の指定辺の実 fiber 四角形を、その同じ辺の宇宙持ち上げへ写す。 -/
def fiberSquareULift {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare s.square
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mp s.zero_corner
  right_edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_rightEdge, s.right_edge]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge_yoneda f).symm
  isPullback := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPullbackSquare_iff_ulift s.square).mp s.isPullback

/-- 元の指定辺の実 cofiber 四角形を、その同じ辺の宇宙持ち上げへ写す。 -/
def cofiberSquareULift {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare s.square
  zero_corner := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mp s.zero_corner
  bottom_edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare_bottomEdge, s.bottom_edge]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge_yoneda f).symm
  isPushout := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift s.square).mp s.isPushout

/-- 元の安定性の三条件は、元の単体集合を任意に宇宙持ち上げしても成立する。 -/
lemma isStable_ulift {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{v, u}).obj X) := by
  refine {
    toHasZeroVertex := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasZeroVertex_iff_ulift.{u, v} X).mp inferInstance
    fiber_exists := ?_
    cofiber_exists := ?_
    fiber_iff_cofiber := ?_ }
  · intro x y e
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    let f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y :=
      ⟨e.edge.down, congrArg ULift.down e.src_eq, congrArg ULift.down e.tgt_eq⟩
    have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f = e := by
      apply SSet.Truncated.Edge.ext
      rfl
    exact ⟨he ▸ fiberSquareULift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare f)⟩
  · intro x y e
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    let f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y :=
      ⟨e.edge.down, congrArg ULift.down e.src_eq, congrArg ULift.down e.tgt_eq⟩
    have he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftEdge.{u, v} f = e := by
      apply SSet.Truncated.Edge.ext
      rfl
    exact ⟨he ▸ cofiberSquareULift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare f)⟩
  · intro t
    have hp := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPullbackSquare_iff_ulift.{u, v} t.down.square
    have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift.{u, v} t.down.square
    rw [t.ulift_down_square] at hp hc
    exact hp.symm.trans ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber t.down).trans hc)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent
