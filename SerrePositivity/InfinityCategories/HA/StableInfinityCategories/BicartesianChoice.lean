module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsomorphismFiberZero
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-! # 双カルテジアン性の fiber/cofiber の選択独立性

概要：同じ辺の cofiber の引き戻し性と fiber の押し出し性は選択によらない。
方針：実四角形の関手同型で普遍性を移し、fiber 側は反対圏で双対化する。
規約：安定性を仮定しない。使われ方：標準 dg 加群四角形からの安定性の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 同じ辺の cofiber の引き戻し性は実四角形の選択によらない。 -/
lemma CofiberSquare.isPullback_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberSquareFunctorIso s t
  exact ⟨fun h => h.of_functorIso e, fun h => h.of_functorIso e.symm⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (isPullback_iff)


/-- 同じ辺の fiber の押し出し性は実四角形の選択によらない。 -/
lemma FiberSquare.isPushout_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_dualSquare s.square).trans
    ((CofiberSquare.isPullback_iff s.opCofiber t.opCofiber).trans
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_dualSquare t.square).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiberSquare (isPushout_iff)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
