module

public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYoneda
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanFamilyJointRealization

/-!
概要：固定した集合値 Yoneda の離散前層への全包含を、同じ二変数の Kan 図式の実現として読む。
方針：既存の Kan 図式族の共同実現の curry の法則に、同じ Yoneda の族を代入する。
  文献対応：HTT 5.1.5.6、Kerodon Corollary 5.6.0.6（Tag 028T）、S8 の固定 Yoneda の全族比較。
規約：元の liftedSetYoneda と discretePresheafInclusion の射を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable (C : Type u) [SmallCategory C]

/-- 元の通常の Yoneda の全族を同じ集合の離散 Kan 複体へ写す。
HTT 5.1.5.6、Kerodon Corollary 5.6.0.6（Tag 028T）、既存の関手の後合成の特殊化。 -/
def kanSetYonedaFamily : C ⥤ Cᵒᵖ ⥤ KanObject.{u} :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) KanObject.{u}).obj setsToKan

/-- 元の Yoneda の nerve と離散図式の束縛の合成は同じ strict な全族の coherent 表示。
HTT 5.1.5.6、Kerodon Corollary 5.6.0.6（Tag 028T）、全高次の係数移送の法則。 -/
lemma liftedSetYoneda_kanDiagram :
    (liftedSetYoneda C ≫ nerveMap (kanDiscretePresheafFunctor C)) ≫
      nerveToCoherent (KanDiagramObject Cᵒᵖ) =
      strictCoherentDiagram (kanSetYonedaFamily C ⋙ kanDiagramBundle) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 固定した離散前層への Yoneda 射は、元の同じ Kan 図式族を実現した全射と一致する。
HTT 5.1.5.6、Kerodon Corollary 5.6.0.6（Tag 028T）、元の公開射を保持する法則。 -/
lemma liftedSetYoneda_realization :
    liftedSetYoneda C ≫ (discretePresheafInclusion C).val =
      strictCoherentDiagram (kanSetYonedaFamily C ⋙ kanDiagramBundle) ≫
        kanDiagramRealization Cᵒᵖ := by
  change liftedSetYoneda C ≫ kanDiscretePresheafMap C = _
  rw [kanDiscretePresheafMap, ← Category.assoc, ← Category.assoc, liftedSetYoneda_kanDiagram]

/-- 固定した離散前層への Yoneda 射は同じ二変数の全 Hom 図式の実現の curry である。
HTT 5.1.5.6、Kerodon Corollary 5.6.0.6（Tag 028T）。全族を一度に比較する。 -/
lemma liftedSetYoneda_realization_curry :
    liftedSetYoneda C ≫ (discretePresheafInclusion C).val =
      curry ((uliftNerveProductSwapIso C Cᵒᵖ).inv ≫
        kanDiagramCoherentNerve (Functor.uncurry.obj (kanSetYonedaFamily C))) := by
  rw [liftedSetYoneda_realization, kanFamily_realization_curry]

end SerrePositivity.InfinityCategories.Sheaves
