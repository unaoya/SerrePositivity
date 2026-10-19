module

public import SerrePositivity.InfinityCategories.F1.LocalizationSourceIso

/-!
概要：初頂点写像の宇宙持ち上げも、持ち上げた指定辺に関する局所化。
方針：持ち上げた底の局所化を、単体圏の nerve の厳密な宇宙比較で移送する。
規約：標的と全パラメーターを、底を持ち上げた共通の宇宙で扱う。
使われ方：全 left fibrations の共同切断評価を coherent に降下する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 任意の宇宙へ持ち上げた初頂点写像も、持ち上げた指定辺に関して局所化を表す。 -/
lemma transportSimplexFirstVertexMap_ulift_isLocalization (B : SSet.{u}) :
    IsLocalization ((SSet.uliftFunctor.{v, u}).map (transportSimplexFirstVertexMap B))
      (ULift.up '' transportSimplexInitialEdges B) := by
  apply isLocalization_of_precomposeIso (transportSimplexNerveUliftIso.{u, v} B) _
    (transportSimplexInitialEdges ((SSet.uliftFunctor.{v, u}).obj B)) _
    (transportSimplexNerveUliftIso_initialEdges_image B)
  rw [transportSimplexNerveUliftIso_firstVertex]
  exact transportSimplexFirstVertexMap_isLocalization _

/-- 宇宙を持ち上げた初頂点写像による、全関手と反転関手の同値。 -/
def transportSimplexUliftLocalizationEquivalence (B : SSet.{u})
    (E : SSet.{max u v}) [Quasicategory E] :
    QCatEquivalence ((ihom ((SSet.uliftFunctor.{v, u}).obj B)).obj E)
      (invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (TransportSimplexCategory B))) E
        (ULift.up '' transportSimplexInitialEdges B) : SSet.{max u v}) :=
  ((transportSimplexFirstVertexMap_ulift_isLocalization.{u, v} B).choose_spec E).choose

/-- 宇宙を持ち上げた反転関手全体から、持ち上げた底上の関手全体への coherent な降下。 -/
def transportSimplexUliftInvertingDescent (B : SSet.{u})
    (E : SSet.{max u v}) [Quasicategory E] :
    (invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (TransportSimplexCategory B))) E
      (ULift.up '' transportSimplexInitialEdges B) : SSet.{max u v}) ⟶
        (ihom ((SSet.uliftFunctor.{v, u}).obj B)).obj E :=
  (transportSimplexUliftLocalizationEquivalence B E).inv

/-- 宇宙を合わせた降下を制限すると、反転関手の全ての族を大域的な関手同型で回収する。 -/
def transportSimplexUliftInvertingDescentFamilyIso (B : SSet.{u})
    (E : SSet.{max u v}) [Quasicategory E] :
    FunctorIso
      (transportSimplexUliftInvertingDescent B E ≫
        (pre ((SSet.uliftFunctor.{v, u}).map (transportSimplexFirstVertexMap B))).app E)
      (invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (TransportSimplexCategory B))) E
        (ULift.up '' transportSimplexInitialEdges B)).ι := by
  have he := FunctorIso.postcomp (transportSimplexUliftLocalizationEquivalence B E).invHomIso
    (invertingFunctors ((SSet.uliftFunctor.{v, u}).obj (nerve (TransportSimplexCategory B))) E
      (ULift.up '' transportSimplexInitialEdges B)).ι
  change FunctorIso
    ((transportSimplexUliftInvertingDescent B E ≫
      localizationPrecomposition ((SSet.uliftFunctor.{v, u}).map (transportSimplexFirstVertexMap B))
        (ULift.up '' transportSimplexInitialEdges B)
        (transportSimplexFirstVertexMap_ulift_isLocalization.{u, v} B).choose E) ≫ _)
    ((𝟙 _) ≫ _) at he
  simpa only [Category.assoc, localizationPrecomposition_ι, Category.id_comp] using he

end SerrePositivity.InfinityCategories
