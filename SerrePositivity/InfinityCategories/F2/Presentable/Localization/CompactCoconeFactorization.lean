module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactInitialFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallQuasicategoryColimitCompact

/-!
概要：小さい compact 図式の全余錐を、filtered 余極限の指定した一段へ因子化する。
方針：図式の compact な余極限を coslice の始対象として用いる。
規約：得られる全余錐間の実辺は、元の filtered 余錐脚そのものを被覆する。
使われ方：HTT 5.5.4.13 の全余錐の因子化の準備。相対境界の延長は別途必要。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 小さい compact 図式の指定余錐を、同じ filtered 余錐脚の上で一段へ因子化する。 -/
lemma compactDiagram_cocone_factorization {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ)
    {A : SSet.{u}} [Quasicategory A] (hA : IsKappaSmall κ A)
    {C : SSet.{u + 1}} [Quasicategory C]
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (hcompact : ∀ a, IsKappaCompact.{u, u + 1} κ (q.app _ a))
    (cq : JoinCocone q) (hcq : IsColimitCone cq)
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (t : (vertexFiber (sliceUnderProjection q) c.vertex) _⦋0⦌) :
    ∃ j : K _⦋0⦌,
      ∃ w : (vertexFiber (sliceUnderProjection q) (D.app _ (ULift.up j))) _⦋0⦌,
      ∃ k : (sliceUnder q).Edge w.val t.val,
        (k.map (sliceUnderProjection q)).edge =
          (coconeTransportLeg c (ULift.up j)).edge := by
  exact compactInitial_leftFibration_factorization (sliceUnderProjection q) cq hcq
    (isKappaCompact_smallQuasicategoryColimit_universe hκ A hA cq hcq hcompact) D c hc t

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
