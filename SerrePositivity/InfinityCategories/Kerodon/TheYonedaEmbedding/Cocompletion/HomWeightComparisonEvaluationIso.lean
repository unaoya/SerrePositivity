module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.HomWeightEvaluatedKanUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.LeftKanUnitPostcompositionHom
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.HomWeightLeftKanEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightYonedaLeftKan

/-!
概要：指定 Yoneda 左 Kan 比較の単位回収式を同じ点評価で運ぶ。
方針：既存の回収式に後合成を適用し、単位回収写像の交換則を使う。
規約：比較射を選び直さない。使われ方：E01 の指定比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LimitsAndColimits.KanExtensions
open Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 概要：点評価した指定単位の普遍性が分かれば、元の比較射の点評価は可逆。
方針：単位回収式と普遍比較同型の一意性を使う。
規約：標的単位の普遍性は別に証明すべき入力として明示する。
使われ方：Kerodon Tag 03M5・03W8・0309、HTT 5.1.3.1・5.1.5.3・4.3.3.7 の
E01 の証明分割。E01 自体の結論の代わりにはしない。 -/
lemma homWeightYonedaLeftKanComparison_evaluation_isIso_of_homUniversal
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C] (F : A ⟶ C)
    {L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity A}
    (β : SSet.Homotopy (yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L))
    (hβ : IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (yonedaInfinityMap A) L β) (a : A _⦋0⦌)
    (hunit : LeftKanHomUniversal ((SSet.uliftFunctor.{u + 1, u}).map F)
      (kanFunctorHomCongr rfl (Category.assoc _ _ _)
        (postcomposeFunctorHom (presheafInfinityEvaluation a) (homWeightYonedaUnit F)))) :
    IsIso (postcomposeFunctorHom (presheafInfinityEvaluation a)
      (homWeightYonedaLeftKanComparison F β hβ)) := by
  let α := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (kanLeftUnitPostcomp β (presheafInfinityEvaluation a)))
  let γ := kanFunctorHomCongr rfl
    (Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map F)
      (presheafHomWeightDiagram F) (presheafInfinityEvaluation a))
    (postcomposeFunctorHom (presheafInfinityEvaluation a) (homWeightYonedaUnit F))
  have hα := homWeightLeftKan_evaluation_homUniversal F β hβ a
  have hf := homWeightYonedaLeftKanComparison_native_evaluation_fac F β hβ a
  have ht := kanFunctorHomCongr_heq rfl
    (Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map F)
      (presheafHomWeightDiagram F) (presheafInfinityEvaluation a))
    (postcomposeFunctorHom (presheafInfinityEvaluation a) (homWeightYonedaUnit F))
  have hh := leftKanHomUniversalIso_hom_unique
    ((SSet.uliftFunctor.{u + 1, u}).map F) α γ hα hunit
    (postcomposeFunctorHom (presheafInfinityEvaluation a)
      (homWeightYonedaLeftKanComparison F β hβ)) (eq_of_heq (hf.trans ht.symm))
  rw [hh]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
