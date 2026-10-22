module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionCofibers
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.Stable.StableOpposite

/-!
概要：安定な元の ∞ 圏の任意の冪等完備化で、全ての指定辺に双カルテジアン fiber が存在。
方針：同じ反転関手の実際の cofiber を双対化し、二重反転を元へ戻す。
規約：元の指定辺を右辺として厳密に保持し、標的の安定性を入力にしない。
使われ方：HA 1.1.3.7 の零角の安定性判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の辺の反転に対する cofiber を、元の指定辺を右辺とする fiber に戻す。 -/
def cofiberOpToFiber {X : SSet.{u}} {x y : X _⦋0⦌}
    {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : CofiberSquare (X := X.op) (edgeOp a)) : FiberSquare a where
  square := dualSquare s.square ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  zero_corner := by
    change IsZeroVertex (SSet.opObjEquiv (squareVertex s.square 0 1))
    exact s.zero_corner.unop
  right_edge := by
    rw [← Category.assoc, dualSquare_rightEdge, s.bottom_edge]
    have hop : reverseSimplex 1 (SSet.yonedaEquiv.symm a.edge) =
        (SSet.yonedaEquiv (X := X.op)).symm (edgeOp a).edge :=
      reverseSimplex_edgeUnop (X := X) (edgeOp a)
    rw [← hop]
    exact reverseSimplex_double 1 _
  isPullback := (isPullbackSquare_iff_postcomp_isIso (dualSquare s.square)
    (SSet.opFunctorCompOpFunctorIso.app X).hom).mp
      ((isPushoutSquare_iff_dualSquare s.square).mp s.isPushout)

/-- 元の反転 cofiber の引き戻し性は、元へ戻した同じ fiber の押し出し性となる。 -/
lemma cofiberOpToFiber_isPushout {X : SSet.{u}} {x y : X _⦋0⦌}
    {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : CofiberSquare (X := X.op) (edgeOp a)) (hs : IsPullbackSquare s.square) :
    IsPushoutSquare (cofiberOpToFiber s).square :=
  (isPushoutSquare_iff_postcomp_isIso (dualSquare s.square)
    (SSet.opFunctorCompOpFunctorIso.app X).hom).mp
      ((isPullbackSquare_iff_dualSquare s.square).mp hs)

/-- 安定な元の圏の任意の冪等完備化の全ての辺には、指定辺を保つ双普遍 fiber が存在。 -/
lemma IsIdempotentCompletion.bicartesian_fiber_exists {C D : SSet.{u}}
    [Quasicategory C] [IsStable C] [Quasicategory D] (f : C ⟶ D)
    (hf : IsIdempotentCompletion f) {x y : D _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj D) x y) :
    ∃ s : FiberSquare a, IsPushoutSquare s.square := by
  obtain ⟨s, hs⟩ := IsIdempotentCompletion.bicartesian_cofiber_exists (SSet.opFunctor.map f)
    (IsIdempotentCompletion.op_general f hf) (edgeOp a)
  exact ⟨cofiberOpToFiber s, cofiberOpToFiber_isPushout s hs⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
