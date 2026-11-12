module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalizationSourceIso

/-!
概要：初頂点写像の宇宙持ち上げも、持ち上げた指定辺に関する局所化。
方針：持ち上げた底の局所化を、単体圏の nerve の厳密な宇宙比較で移送する。
規約：標的と全パラメーターを、底を持ち上げた共通の宇宙で扱う。
使われ方：全 left fibrations の共同切断評価を coherent に降下する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 任意の宇宙へ持ち上げた初頂点写像も、持ち上げた指定辺に関して局所化を表す。 -/
lemma transportSimplexFirstVertexMap_ulift_isLocalization (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B))
      (ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLocalization_of_precomposeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexNerveUliftIso.{u, v} B) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges ((SSet.uliftFunctor.{v, u}).obj B)) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexNerveUliftIso_initialEdges_image B)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexNerveUliftIso_firstVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_isLocalization _

/-- 宇宙を持ち上げた初頂点写像による、全関手と反転関手の同値。 -/
def transportSimplexUliftLocalizationEquivalence (B : SSet.{u})
    (E : SSet.{max u v}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom ((SSet.uliftFunctor.{v, u}).obj B)).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))) E
        (ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B) : SSet.{max u v}) :=
  ((transportSimplexFirstVertexMap_ulift_isLocalization.{u, v} B).choose_spec E).choose

/-- 宇宙を持ち上げた反転関手全体から、持ち上げた底上の関手全体への coherent な降下。 -/
def transportSimplexUliftInvertingDescent (B : SSet.{u})
    (E : SSet.{max u v}) [Quasicategory E] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))) E
      (ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B) : SSet.{max u v}) ⟶
        (ihom ((SSet.uliftFunctor.{v, u}).obj B)).obj E :=
  (transportSimplexUliftLocalizationEquivalence B E).inv

/-- 宇宙を合わせた降下を制限すると、反転関手の全ての族を大域的な関手同型で回収する。 -/
def transportSimplexUliftInvertingDescentFamilyIso (B : SSet.{u})
    (E : SSet.{max u v}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (transportSimplexUliftInvertingDescent B E ≫
        (pre ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B))).app E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))) E
        (ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B)).ι := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (transportSimplexUliftLocalizationEquivalence B E).invHomIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))) E
      (ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B)).ι
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((transportSimplexUliftInvertingDescent B E ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B))
        (ULift.up '' _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B)
        (transportSimplexFirstVertexMap_ulift_isLocalization.{u, v} B).choose E) ≫ _)
    ((𝟙 _) ≫ _) at he
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, Category.id_comp] using he

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
