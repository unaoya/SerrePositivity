module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.HomWeightComparisonEvaluationFac
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

/-- 概要：指定比較射の点評価は同じ点評価した単位を回収する。
方針：元の回収式と前後合成の交換則をつなぐ。
規約：任意の候補 L、指定 β、元の比較射を保持する。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3 に対応する
E01 の指定比較の計算法則。 -/
lemma homWeightYonedaLeftKanComparison_native_evaluation_fac {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C)
    {L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity A}
    (β : SSet.Homotopy (yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L))
    (hβ : IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (yonedaInfinityMap A) L β) (a : A _⦋0⦌) :
    HEq (leftKanHomMap ((SSet.uliftFunctor.{u + 1, u}).map F)
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (kanLeftUnitPostcomp β (presheafInfinityEvaluation a))))
      (presheafHomWeightDiagram F ≫ presheafInfinityEvaluation a)
      (postcomposeFunctorHom (presheafInfinityEvaluation a)
        (homWeightYonedaLeftKanComparison F β hβ)))
      (postcomposeFunctorHom (presheafInfinityEvaluation a) (homWeightYonedaUnit F)) := by
  have h := homWeightYonedaLeftKanComparison_evaluation_fac F β hβ a
  rw [kanLeftUnitPostcomp_hom] at h
  exact h

/-- 概要：同じ点評価した標準単位は Hom の普遍写像性を持つ。
方針：指定単位の左 Kan 保存則を既存の Hom 普遍性へ渡す。
規約：単位を選び直さない。
使われ方：Kerodon Tag 03M5・03W8・0309、HTT 5.1.3.1・5.1.5.3・4.3.3.7 の
E01 の指定比較の一意性に渡す入力。 -/
lemma homWeightLeftKan_evaluation_homUniversal {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C)
    {L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity A}
    (β : SSet.Homotopy (yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L))
    (hβ : IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (yonedaInfinityMap A) L β) (a : A _⦋0⦌) :
    LeftKanHomUniversal ((SSet.uliftFunctor.{u + 1, u}).map F)
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (kanLeftUnitPostcomp β (presheafInfinityEvaluation a)))) :=
  kanLeftKanExtension_homUniversal _ _ (homWeightLeftKan_evaluation F β hβ a)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
