module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutComparisonInvertible
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanZeroBranchIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-! # 指定した射の cofiber 四角形の比較同型

概要：同じ辺の二つの cofiber 四角形は関手として同型であり、cofiber 頂点も同型である。
方針：同じ第一枝と終対象へ向かう第二枝の span の同型を押し出し全体へ延長する。
規約：安定性は不要。使われ方：cofiber の零性の選択独立性と射の同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：同じ辺の二つの cofiber 四角形は図式として同型である。
方針：第一枝を固定した span の同型を、押し出し全体の同型へ延長する。
規約：値域は quasicategory、安定性は不要。使われ方：cofiber 対象の比較同型。 -/
lemma nonempty_cofiberSquareFunctorIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.square t.square) := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_functorIso_span_of_first_eq_terminal_second
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc horn₂₀.ι₀₁,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, s.bottom_edge, ← Category.assoc horn₂₀.ι₀₁,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, t.bottom_edge])
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
        ((horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ s.square)).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
      exact s.zero_corner.2)
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
        ((horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ t.square)).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
      exact t.zero_corner.2)
  obtain ⟨d, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutSquareFunctorIso_lift_span
    s.square t.square s.isPushout t.isPushout e
  exact ⟨d⟩

/-- 概要：同じ辺の二つの cofiber 対象はホモトピー圏で同型である。
方針：四角形の比較同型を終端頂点で評価する。
規約：値域は quasicategory。使われ方：cofiber の零性の輸送。 -/
def cofiberSquareComparisonIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso s.cofiber t.cofiber := by
  let e := Classical.choice (nonempty_cofiberSquareFunctorIso s t)
  let v : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v
  have hs : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square) = s.cofiber := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    rfl
  have ht : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square) = t.cofiber := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    rfl
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e q ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk ht)

/-- 概要：指定した辺の cofiber の零性は cofiber 四角形の選択によらない。
方針：比較同型とその逆で零頂点を移す。
規約：安定性は不要。使われ方：選んだ cofiber による同型判定の独立性。 -/
lemma cofiberSquare_zero_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex s.cofiber ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex t.cofiber :=
  ⟨fun h => h.of_vertexIso (cofiberSquareComparisonIso s t),
    fun h => h.of_vertexIso (cofiberSquareComparisonIso s t).symm⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
