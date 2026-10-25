module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.JointRealizationReindex
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange

/-!
概要：元の相対切断底変換比較の添字制限を指定実現同型まで回収する。
方針：比較データの厳密な制限と、既存定義の端点移送を正規化する。
規約：元の底変換比較と元の実現同型を保持する。
使われ方：P-12 の単体添字上の指定底変換合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：相対切断の元の底変換比較は添字制限を厳密に保つ。
方針：元の比較成分と自然性の定義を計算する。
規約：全比較データの等式。使われ方：単体添字の制限への特殊化。 -/
lemma relativeSectionBaseChangeComparison_reindex {B D : SSet.{u}}
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (H : L ⥤ J) :
    jointComparisonReindex (relativeSectionBaseChangeComparison k A) H =
      relativeSectionBaseChangeComparison k (H.op ⋙ A) := rfl

/-- 概要：元の底変換実現同型は共同実現同型の端点正規化である。
方針：既存定義の書き換えを異種等式として取り出す。
規約：既存の指定同型を変更しない。使われ方：全自然な添字制限式の正規化。 -/
lemma relativeSectionBaseChangeRealizationIso_normalized {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    relativeSectionBaseChangeRealizationIso k A =
      diagramIsoCongr ((relativeSectionEnrichedDiagram A).realization_precompose
        (leftFibrationBaseChangeEnriched k)) rfl
        ((relativeSectionBaseChangeComparison k A).realizationIso
          (relativeSectionBaseChangeComparison_isQCatEquivalence k A)) := by
  have he : HEq (relativeSectionBaseChangeRealizationIso k A)
      ((relativeSectionBaseChangeComparison k A).realizationIso
        (relativeSectionBaseChangeComparison_isQCatEquivalence k A)) := by
    unfold relativeSectionBaseChangeRealizationIso
    dsimp only [_root_.id]
    have hcast {T U : Sort (u + 2)} (h : T = U) (z : T) : HEq (Eq.mp h z) z := by
      cases h
      rfl
    exact hcast _ _
  exact eq_of_heq (he.trans (diagramIsoCongr_heq _ _ _).symm)

/-- 概要：相対切断の元の指定底変換同型は全添字制限と両立する。
方針：全共同図式での制限の式を元の両端へ正規化する。
規約：全図式の同型として同定する。使われ方：単体切断の合成の添字照合。 -/
lemma relativeSectionBaseChangeRealizationIso_reindex {B D : SSet.{u}}
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (H : L ⥤ J) :
    relativeSectionBaseChangeRealizationIso k (H.op ⋙ A) =
      diagramIsoCongr
        (congrArg (fun f ↦ leftFibrationInfinityBaseChange k ≫ f)
          ((relativeSectionEnrichedDiagram A).realization_reindex H))
        ((relativeSectionEnrichedDiagram (A ⋙ Over.map k)).realization_reindex H)
        ((relativeSectionBaseChangeRealizationIso k A).postcomp
          ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))).app SpaceInfinity.{u})) := by
  rw [relativeSectionBaseChangeRealizationIso_normalized k (H.op ⋙ A)]
  change diagramIsoCongr
    (((relativeSectionEnrichedDiagram A).reindex H).realization_precompose
      (leftFibrationBaseChangeEnriched k)) rfl
    ((jointComparisonReindex (relativeSectionBaseChangeComparison k A) H).realizationIso
      (jointComparisonReindex_isQCatEquivalence _ H
        (relativeSectionBaseChangeComparison_isQCatEquivalence k A))) = _
  rw [jointRealizationIso_reindex (relativeSectionBaseChangeComparison k A) H
    (relativeSectionBaseChangeComparison_isQCatEquivalence k A), diagramIsoCongr_comp]
  rw [relativeSectionBaseChangeRealizationIso_normalized k A,
    diagramIsoCongr_postcomp, diagramIsoCongr_comp]

end SerrePositivity.InfinityCategories.F2.Presentable
