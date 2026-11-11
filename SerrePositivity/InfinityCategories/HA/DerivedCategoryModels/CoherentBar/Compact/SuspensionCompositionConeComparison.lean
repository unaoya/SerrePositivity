module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionConeRepresentativeComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SuspensionModuleCompositionIso
public import SerrePositivity.KST.SConstruction.DGFunctorWhiskering
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence

/-!
概要：固定合成 data と固定 data 二本の合成を、実加群評価の全 Hom end で比較する。
方針：代表の共役、加群延長の合成比較、および全次数の前後合成を使う。
規約：固定 cell 分解と指定 ε 商への持ち上げは別の境界である。
使われ方：固定入力射の合成比較を構成する際の実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 固定合成 data と二本の固定 data の合成の、実加群評価後の全 Hom 自然な閉同型。 -/
def dgSuspensionCompositionConeEvaluationIso
    {A B C : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (g : B ⟶ C) :
    ForgetEnrichment.of (Complex R)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (f ≫ g)).cone.comp
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeEvaluation R κ hκ C)) ≅
      ForgetEnrichment.of (Complex R)
        (((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).cone.comp
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).cone).comp
            (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeEvaluation R κ hκ C)) := by
  let EA := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeEvaluation R κ hκ A
  let EB := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeEvaluation R κ hκ B
  let EC := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeEvaluation R κ hκ C
  let JF := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).cone
  let JG := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ g).cone
  let EG := dgModuleExtension R B C g.down
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeRepresentativeIso R κ hκ (f ≫ g)).symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgModuleCompositionPrecompositionIso R A B C f.down g.down EA).symm ≪≫
    ((dgFunctorPostDG R _ _ _ EG).onClosed.mapIso
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeRepresentativeIso R κ hκ f)) ≪≫
    eqToIso (congrArg (ForgetEnrichment.of (Complex R))
      (strictDGFunctor_comp_assoc JF EB EG)) ≪≫
    ((dgFunctorPreDG R _ _ _ JF).onClosed.mapIso
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionConeRepresentativeIso R κ hκ g)) ≪≫
    (eqToIso (congrArg (ForgetEnrichment.of (Complex R))
      (strictDGFunctor_comp_assoc JF JG EC))).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
