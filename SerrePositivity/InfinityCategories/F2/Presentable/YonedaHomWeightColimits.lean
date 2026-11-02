module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseColimits
public import SerrePositivity.InfinityCategories.F2.Compact.YonedaEvaluationClassification
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：元の Yoneda を係数に持つ全 Hom 前層値関手は、小さい coherent 余極限を保つ。
方針：元の各点評価を全係数 Yoneda 比較へ移し、空間の指定宇宙変更の保存性を使う。
規約：指定全余錐を保持し、対象ごとの比較を大域自然同型と同一視しない。
使われ方：密度による全前層上の Yoneda 評価比較の左 Kan 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：元の全 Yoneda Hom 係数関手は、指定された小さい coherent 余極限全余錐を保つ。
方針：元の各点評価を全係数 Yoneda 比較へ移し、空間の指定宇宙変更の保存性を使う。
規約：指定全余錐を保持し、対象ごとの比較を大域自然同型と同一視しない。
使われ方：密度による全前層上の Yoneda 評価比較の左 Kan 条件。 -/
lemma yonedaHomWeightDiagram_map_isColimit {I C : SSet.{u}}
    [Quasicategory I] [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafInfinity C)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (presheafHomWeightDiagram (yonedaInfinityMap C))
      (JoinCocone.ulift.{u + 1, u + 2} c)) := by
  apply presheafInfinity_isColimit_of_evaluation _ _
  rintro ⟨y⟩
  have he := presheafHomWeightDiagram_evaluationIso (yonedaInfinityMap C) (ULift.up y) ≪≫
    F2.Compact.yonedaInfinityMap_evaluationIso y
  have hd := F2.Compact.spaceUniverseDiagram_map_isColimit
    (D ≫ presheafInfinityEvaluation y) _
      (presheafInfinity_evaluation_isColimit D c hc y)
  change IsColimitCone (mapJoinCocone F2.Compact.spaceUniverseDiagram
    (JoinCocone.ulift.{u + 1, u + 2} (mapJoinCocone (presheafInfinityEvaluation y) c))) at hd
  rw [← F2.Compact.mapJoinCocone_universe_comp] at hd
  change IsColimitCone (mapJoinCocone
    (presheafHomWeightDiagram (yonedaInfinityMap C) ≫
      presheafInfinityEvaluation (ULift.up y)) (JoinCocone.ulift.{u + 1, u + 2} c))
  exact hd.of_functorIso ((FunctorIso.precomp he (JoinCocone.ulift.{u + 1, u + 2} c).val).symm)

end SerrePositivity.InfinityCategories.HomotopyLimits
