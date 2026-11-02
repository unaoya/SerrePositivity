module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitActionConjugacy

/-!
概要：元の上下作用の比較から、同じ上側 native 因子をその逆で消去する。
方針：元の指定共役式へ同じ native 因子の逆を合成する。
規約：元の指定因子を保持。使われ方：a6 の模型正方形の上側外側因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の native 因子の逆を合成すると、下側輸送・同じ二面比較・上側単位だけが残る。 -/
lemma coherentColimitActionComparison_cancel_upperNative :
    ((coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H) ≪≫
      (coherentColimitUpperNativeFactorIso B H).symm =
    (coherentColimitLowerTransportFactorIso B H).symm ≪≫
      coherentColimitNativeTriangleActionComparison B H ≪≫
        coherentColimitUpperUnitFactorIso B H := by
  rw [coherentColimitActionComparison_eq_conjugate, coherentColimitUpperTransportFactorIso]
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

end SerrePositivity.InfinityCategories.F2
