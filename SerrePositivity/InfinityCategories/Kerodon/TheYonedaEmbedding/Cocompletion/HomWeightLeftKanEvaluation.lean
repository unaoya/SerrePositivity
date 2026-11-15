module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafEvaluationReindexedColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction

/-!
概要：元の Yoneda 左 Kan 単位を点評価しても、その局所普遍性を保つ。
方針：指定された局所余錐輸送を評価し、小さい局所形状との同型で余極限性を運ぶ。
規約：元の単位と全輸送を使う。使われ方：E01 の同じ比較射の点評価。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LimitsAndColimits.KanExtensions
open Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
open Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 概要：元の指定 Yoneda 左 Kan 単位の点評価は同じ射に沿う左 Kan 単位。
方針：元の局所輸送を評価し、形状の宇宙同型を介して余極限保存を適用する。
規約：任意の L と指定 β を保持する。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3に対応する
Yoneda 比較の E01 の、指定単位の評価に関する法則。 -/
lemma homWeightLeftKan_evaluation {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C)
    {L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity A}
    (β : SSet.Homotopy (yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L))
    (hβ : IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (yonedaInfinityMap A) L β) (a : A _⦋0⦌) :
    IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (yonedaInfinityMap A ≫ presheafInfinityEvaluation a)
      (L ≫ presheafInfinityEvaluation a)
      (kanLeftUnitPostcomp β (presheafInfinityEvaluation a)) := by
  intro c
  rcases c with ⟨c⟩
  obtain ⟨t, ht⟩ := hβ (ULift.up c)
  refine ⟨kanLeftTransportPostcomp t (presheafInfinityEvaluation a), ?_⟩
  have he := presheafEvaluation_isColimit_of_shapeIso
    (leftKanShapeUniverseIso.{u, u + 1} F c) t.cocone ht a
  apply (isColimitCone_iff_of_cocone_val_eq _
    (mapJoinCocone (presheafInfinityEvaluation a) t.cocone) ?_).mpr he
  exact kanLeftTransportPostcomp_cocone_val t (presheafInfinityEvaluation a)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
