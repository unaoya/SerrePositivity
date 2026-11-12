module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperTransportFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeActionPresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerHEq

/-!
概要：既存の上側 native 因子を、元の全 Hom 成分と指定余錐比較の合成の逆へ戻す。
方針：元の単位の持ち上げ表示の等式移送だけを除く。
規約：元の a6 の比較を保持。使われ方：同じ全 Hom の自然性を上側因子へ適用する。
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
local notation "a" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)

/-- 既存の上側 native 因子は、元の二つの指定全 Hom 成分の合成の同じ逆。 -/
lemma coherentColimitUpperNativeFactorIso_heq_components :
    HEq (coherentColimitUpperNativeFactorIso B H)
      (coherentTotalMapNativeActionComponentsIso F G a).symm := by
  unfold coherentColimitUpperNativeFactorIso
  refine (functorIso_symm_heq_of_heq (coherentTotalMapNativeActionIso F G a)
    (functorIsoOfEq (coherentTotalMapNativeActionIso F G a) rfl
      (coherentColimitNativeAction_unit_lift B H)) rfl
    (coherentColimitNativeAction_unit_lift B H) (functorIsoOfEq_heq _ _ _)).trans ?_
  exact coherentTotalMapNativeActionIso_symm_heq_components F G a

end SerrePositivity.InfinityCategories.F2
