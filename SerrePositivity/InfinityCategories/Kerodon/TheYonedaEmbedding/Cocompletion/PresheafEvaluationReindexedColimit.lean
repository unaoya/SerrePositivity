module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：小さい形状の宇宙変更と同型な形状で、同じ前層余錐の評価を保存する。
方針：形状同型による再添字付けの前後で既存の点別余極限判定を運ぶ。
規約：元の余錐と指定評価を保持する。
使われ方：E01 の局所左 Kan 形状の宇宙比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LimitsAndColimits.LimitsAndColimits
open Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 概要：小さい宇宙変更形状と同型な形状の前層余極限は点評価で保存される。
方針：同じ余錐を指定同型で再添字付けして、点別余極限保存を適用し戻す。
規約：形状の小ささの同型を明示し、元の余錐を使う。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3の
Yoneda 比較の局所入力で使う、既存の点評価保存の係数移送。 -/
lemma presheafEvaluation_isColimit_of_shapeIso {B A : SSet.{u}} {J : SSet.{u + 1}}
    (e : (SSet.uliftFunctor.{u + 1, u}).obj B ≅ J)
    {p : J ⟶ PresheafInfinity A} (c : JoinCocone p) (hc : IsColimitCone c)
    (a : A _⦋0⦌) : IsColimitCone (mapJoinCocone (presheafInfinityEvaluation a) c) := by
  have hr := (isColimitCone_iff_reindexIso c e).mp hc
  have he := presheafInfinity_evaluation_isColimit (e.hom ≫ p) (c.reindexIso e) hr a
  apply (isColimitCone_iff_reindexIso
    (mapJoinCocone (presheafInfinityEvaluation a) c) e).mpr
  apply (isColimitCone_iff_of_cocone_val_eq _
    (mapJoinCocone (presheafInfinityEvaluation a) (c.reindexIso e)) ?_).mpr he
  change joinMap e.hom (𝟙 _) ≫ (c.val ≫ presheafInfinityEvaluation a) =
    (joinMap e.hom (𝟙 _) ≫ c.val) ≫ presheafInfinityEvaluation a
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
