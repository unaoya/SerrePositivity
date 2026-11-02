module
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.Stable.IsomorphismFiberZero
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-! # 双カルテジアン性の fiber/cofiber の選択独立性

概要：同じ辺の cofiber の引き戻し性と fiber の押し出し性は選択によらない。
方針：実四角形の関手同型で普遍性を移し、fiber 側は反対圏で双対化する。
規約：安定性を仮定しない。使われ方：標準 dg 加群四角形からの安定性の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 同じ辺の cofiber の引き戻し性は実四角形の選択によらない。 -/
lemma CofiberSquare.isPullback_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : CofiberSquare f) : IsPullbackSquare s.square ↔ IsPullbackSquare t.square := by
  obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso s t
  exact ⟨fun h => h.of_functorIso e, fun h => h.of_functorIso e.symm⟩

/-- 同じ辺の fiber の押し出し性は実四角形の選択によらない。 -/
lemma FiberSquare.isPushout_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : FiberSquare f) : IsPushoutSquare s.square ↔ IsPushoutSquare t.square := by
  exact (isPushoutSquare_iff_dualSquare s.square).trans
    ((CofiberSquare.isPullback_iff s.opCofiber t.opCofiber).trans
      (isPushoutSquare_iff_dualSquare t.square).symm)

end SerrePositivity.InfinityCategories
