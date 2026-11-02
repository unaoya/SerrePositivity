module

public import SerrePositivity.InfinityCategories.Core.UniverseZeroTriangle

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
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の指定辺の実 fiber 四角形を、その同じ辺の宇宙持ち上げへ写す。 -/
def fiberSquareULift {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : FiberSquare f) :
    FiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f) where
  square := uliftSquare s.square
  zero_corner := by
    rw [uliftSquare_vertex]
    exact (isZeroVertex_iff_ulift _).mp s.zero_corner
  right_edge := by
    rw [uliftSquare_rightEdge, s.right_edge]
    exact (uliftEdge_yoneda f).symm
  isPullback := (isPullbackSquare_iff_ulift s.square).mp s.isPullback

/-- 元の指定辺の実 cofiber 四角形を、その同じ辺の宇宙持ち上げへ写す。 -/
def cofiberSquareULift {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s : CofiberSquare f) :
    CofiberSquare (X := (SSet.uliftFunctor.{v, u}).obj X) (uliftEdge.{u, v} f) where
  square := uliftSquare s.square
  zero_corner := by
    rw [uliftSquare_vertex]
    exact (isZeroVertex_iff_ulift _).mp s.zero_corner
  bottom_edge := by
    rw [uliftSquare_bottomEdge, s.bottom_edge]
    exact (uliftEdge_yoneda f).symm
  isPushout := (isPushoutSquare_iff_ulift s.square).mp s.isPushout

/-- 元の安定性の三条件は、元の単体集合を任意に宇宙持ち上げしても成立する。 -/
lemma isStable_ulift {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    IsStable ((SSet.uliftFunctor.{v, u}).obj X) := by
  refine {
    toHasZeroVertex := (hasZeroVertex_iff_ulift.{u, v} X).mp inferInstance
    fiber_exists := ?_
    cofiber_exists := ?_
    fiber_iff_cofiber := ?_ }
  · intro x y e
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    let f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y :=
      ⟨e.edge.down, congrArg ULift.down e.src_eq, congrArg ULift.down e.tgt_eq⟩
    have he : uliftEdge.{u, v} f = e := by
      apply SSet.Truncated.Edge.ext
      rfl
    exact ⟨he ▸ fiberSquareULift (chosenFiberSquare f)⟩
  · intro x y e
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    let f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y :=
      ⟨e.edge.down, congrArg ULift.down e.src_eq, congrArg ULift.down e.tgt_eq⟩
    have he : uliftEdge.{u, v} f = e := by
      apply SSet.Truncated.Edge.ext
      rfl
    exact ⟨he ▸ cofiberSquareULift (chosenCofiberSquare f)⟩
  · intro t
    have hp := isPullbackSquare_iff_ulift.{u, v} t.down.square
    have hc := isPushoutSquare_iff_ulift.{u, v} t.down.square
    rw [t.ulift_down_square] at hp hc
    exact hp.symm.trans ((IsStable.fiber_iff_cofiber t.down).trans hc)

end SerrePositivity.InfinityCategories.F2.Idempotent
