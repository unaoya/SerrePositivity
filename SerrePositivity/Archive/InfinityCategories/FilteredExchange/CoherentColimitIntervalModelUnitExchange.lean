module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalModelUnitComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の模型単位比較の下側因子を戻し、中央比較と上側単位との交換式を保持する。
方針：元の指定三因子式の左に同じ下側因子を合成して相殺する。
規約：a6 の模型比較を再選択しない。使われ方：最後辺の上側単位因子の消去。
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

/-- 同じ中央比較と上側単位の合成は、元の下側因子と a6 の同じ模型単位比較に等しい。 -/
lemma coherentColimitIntervalModelUnitComparison_exchange :
    coherentColimitNativeTriangleActionComparison B H ≪≫ coherentColimitUpperUnitFactorIso B H =
      coherentColimitLowerTransportFactorIso B H ≪≫
        coherentColimitIntervalModelUnitComparison B H := by
  have h := congrArg (fun e => coherentColimitLowerTransportFactorIso B H ≪≫ e)
    (coherentColimitIntervalModelUnitComparison_eq_reduced B H)
  simpa only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans] using h.symm

/-- 元の交換式は、任意の実始域射による前合成でも同じ指定比較の値を保つ。 -/
lemma coherentColimitIntervalModelUnitComparison_precomp_exchange {A : SSet.{u + 1}}
    (f : A ⟶ leftUnstraightening F) :
    (coherentColimitNativeTriangleActionComparison B H).precomp f ≪≫
      (coherentColimitUpperUnitFactorIso B H).precomp f =
    (coherentColimitLowerTransportFactorIso B H).precomp f ≪≫
      (coherentColimitIntervalModelUnitComparison B H).precomp f := by
  have h := congrArg (fun e => FunctorIso.precomp e f)
    (coherentColimitIntervalModelUnitComparison_exchange B H)
  simpa only [functorIso_precomp_trans] using h

end SerrePositivity.InfinityCategories.F2
