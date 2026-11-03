module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitActionConjugacy
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFiberTransportRecovery

/-!
概要：a6 の既存の fiber 比較の同じ前合成の値を、元の二面比較の指定共役式へ戻す。
方針：既存の充満忠実な逆像の回収と、上下作用の指定因子の厳密な式を合成する。
規約：fiber 比較も二面も選び直さない。使われ方：指定 path の整合の反映。
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

/-- 既存の a6 の fiber 比較の像は、元の二面比較の元の指定因子による共役と値まで一致する。 -/
lemma coherentColimitFiberTransportComparisonIso_precomp_heq_conjugate :
    HEq ((coherentColimitFiberTransportComparisonIso B H).precomp
      (coconeFiberMap (coherentDiagramTotalCocone F)))
      ((coherentColimitLowerTransportFactorIso B H).symm ≪≫
        coherentColimitNativeTriangleActionComparison B H ≪≫
          coherentColimitUpperTransportFactorIso B H) :=
  (coherentColimitFiberTransportComparisonIso_precomp_heq B H).trans
    (heq_of_eq (coherentColimitActionComparison_eq_conjugate B H))

/-- 同じ native 作用の端点等式を反映すると、既存の fiber 比較の像を等式で回収する。 -/
lemma coherentColimitFiberTransportComparisonIso_precomp_eq_conjugate :
    (coherentColimitFiberTransportComparisonIso B H).precomp
        (coconeFiberMap (coherentDiagramTotalCocone F)) =
      functorIsoOfEq ((coherentColimitLowerTransportFactorIso B H).symm ≪≫
        coherentColimitNativeTriangleActionComparison B H ≪≫
          coherentColimitUpperTransportFactorIso B H) rfl
        (coherentTotalMapNativeAction_eq F G
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) := by
  apply eq_of_heq
  exact (coherentColimitFiberTransportComparisonIso_precomp_heq_conjugate B H).trans
    (functorIsoOfEq_heq _ rfl _).symm

end SerrePositivity.InfinityCategories.F2
