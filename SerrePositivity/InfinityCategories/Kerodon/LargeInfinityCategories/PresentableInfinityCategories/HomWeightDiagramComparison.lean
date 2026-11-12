module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullPresheafHomWeightFamily

/-!
概要：元の小図式に沿う全前層 Hom 係数族と、実際の標的 Hom 図式の比較。
方針：全自然な Yoneda・Ind 制限同型を同じ元の図式に前合成する。
規約：同じ全図式と全標的係数を保持する。
使われ方：密度側と simplicial Ind 側の Hom 極限の移送。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：持ち上げた全 Hom 族は元の図式の前合成と可換。
方針：元の宇宙変更と反転の合成保存を使う。
規約：同じ全写像の等式である。
使われ方：小図式に沿う全自然比較の正規化。 -/
lemma canonicalLiftedHomFamily_precomp {K A D : SSet.{u}} [Quasicategory D]
    (i : K ⟶ A) (G : A ⟶ D) :
    (SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map
      ((SSet.uliftFunctor.{u + 1, u}).map i)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily (i ≫ G) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily, Functor.map_comp, Category.assoc]

variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：元の表現可能図式に沿う全係数族は同じ標的 Hom 図式と全自然同型。
方針：全 Yoneda 制限同型に同じ小図式を前合成する。
規約：元の C 上の全図式を保持する。
使われ方：密度余錐の Hom 極限の元の図式への移送。 -/
def fullPresheafHomWeightFamily_yonedaDiagramIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    {E : SSet.{u}} (p : E ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map
          ((SSet.uliftFunctor.{u + 1, u}).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily ((SSet.uliftFunctor.{u + 1, u}).map p ≫ F₀)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily_yonedaRestrictionIso F₀ ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily_evaluationIso F₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homWeightEvaluationFamily_liftedIso F₀
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
    ((SSet.uliftFunctor.{u + 2, u + 1}).map ((SSet.uliftFunctor.{u + 1, u}).map p))))
  simpa only [Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftedHomWeightFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily] using h

/-- 概要：元の Ind 図式に沿う全係数族は、同じ延長像の標的 Hom 図式と全自然同型。
方針：元の全 Ind Hom 比較を同じ小図式へ制限する。
規約：全標的係数の自然性を保持する。
使われ方：bar の幾何学的実現側の Hom 極限の比較。 -/
def fullPresheafHomWeightFamily_indDiagramIso (κ : Cardinal.{u})
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) F₀ G β)
    {E : SSet.{u}} (p : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily (p ≫ G)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indExtensionHomWeight_liftedIso κ β hβ).precomp
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
      ((SSet.uliftFunctor.{u + 2, u + 1}).map p)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.canonicalLiftedHomFamily_precomp] at e
  simpa only [Functor.map_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullPresheafHomWeightFamily_indRestriction] using e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
