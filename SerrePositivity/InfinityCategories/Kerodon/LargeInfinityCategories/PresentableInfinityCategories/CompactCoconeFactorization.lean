module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactInitialFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SmallQuasicategoryColimitCompact

/-!
概要：小さい compact 図式の全余錐を、filtered 余極限の指定した一段へ因子化する。
方針：図式の compact な余極限を coslice の始対象として用いる。
規約：得られる全余錐間の実辺は、元の filtered 余錐脚そのものを被覆する。
使われ方：HTT 5.5.4.13 の全余錐の因子化の準備。相対境界の延長は別途必要。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 小さい compact 図式の指定余錐を、同じ filtered 余錐脚の上で一段へ因子化する。 -/
lemma compactDiagram_cocone_factorization {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ)
    {A : SSet.{u}} [Quasicategory A] (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A)
    {C : SSet.{u + 1}} [Quasicategory C]
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (hcompact : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (q.app _ a))
    (cq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hcq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cq)
    {K : SSet.{u}} [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) c.vertex) _⦋0⦌) :
    ∃ j : K _⦋0⦌,
      ∃ w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) (D.app _ (ULift.up j))) _⦋0⦌,
      ∃ k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q).Edge w.val t.val,
        (k.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)).edge =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up j)).edge := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactInitial_leftFibration_factorization (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) cq hcq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hκ A hA cq hcq hcompact) D c hc t

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
