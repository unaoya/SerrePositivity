module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionCofibers
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite

/-!
概要：安定な元の ∞ 圏の任意の冪等完備化で、全ての指定辺に双カルテジアン fiber が存在。
方針：同じ反転関手の実際の cofiber を双対化し、二重反転を元へ戻す。
規約：元の指定辺を右辺として厳密に保持し、標的の安定性を入力にしない。
使われ方：HA 1.1.3.7 の零角の安定性判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の辺の反転に対する cofiber を、元の指定辺を右辺とする fiber に戻す。 -/
def cofiberOpToFiber {X : SSet.{u}} {x y : X _⦋0⦌}
    {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a)) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare a where
  square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  zero_corner := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 0 1))
    exact s.zero_corner.unop
  right_edge := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_rightEdge, s.bottom_edge]
    have hop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 (SSet.yonedaEquiv.symm a.edge) =
        (SSet.yonedaEquiv (X := X.op)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a).edge :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.reverseSimplex_edgeUnop (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a)
    rw [← hop]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_double 1 _
  isPullback := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square)
    (SSet.opFunctorCompOpFunctorIso.app X).hom).mp
      ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_dualSquare s.square).mp s.isPushout)

/-- 元の反転 cofiber の引き戻し性は、元へ戻した同じ fiber の押し出し性となる。 -/
lemma cofiberOpToFiber_isPushout {X : SSet.{u}} {x y : X _⦋0⦌}
    {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a)) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (cofiberOpToFiber s).square :=
  (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square)
    (SSet.opFunctorCompOpFunctorIso.app X).hom).mp
      ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare s.square).mp hs)

/-- 安定な元の圏の任意の冪等完備化の全ての辺には、指定辺を保つ双普遍 fiber が存在。 -/
lemma IsIdempotentCompletion.bicartesian_fiber_exists {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D] (f : C ⟶ D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) {x y : D _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj D) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square := by
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.bicartesian_cofiber_exists (SSet.opFunctor.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op_general f hf) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a)
  exact ⟨cofiberOpToFiber s, cofiberOpToFiber_isPushout s hs⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
