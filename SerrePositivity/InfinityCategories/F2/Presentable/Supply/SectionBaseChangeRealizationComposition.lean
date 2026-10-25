module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.SectionDiagramBaseChangeReindex

/-!
概要：元の相対切断底変換の指定実現同型の合成則。
方針：標準反復 pullback 比較の共同実現と、二つの元の実現同型を正規化する。
規約：元の pullback 比較と元の底変換同型を保持する。
使われ方：P-12 の指定 straightening 底変換合成則の降下前の式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：反復底変換の切断実現の端点を元の二つの関手の合成に揃える。
方針：豊穣前合成の実現の公式を二回使う。
規約：対象ごとの同型を使わない。使われ方：共同標準比較の端点正規化。 -/
lemma sectionBaseChangeIteratedRealization {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    ((relativeSectionEnrichedDiagram A).precompose
      ((leftFibrationBaseChangeEnriched k).comp SSet
        (leftFibrationBaseChangeEnriched l))).realization =
      leftFibrationInfinityBaseChange k ≫ leftFibrationInfinityBaseChange l ≫
        (relativeSectionEnrichedDiagram A).realization :=
  (((relativeSectionEnrichedDiagram A).precompose
    (leftFibrationBaseChangeEnriched l)).realization_precompose
    (leftFibrationBaseChangeEnriched k)).trans
      (congrArg (fun f ↦ leftFibrationInfinityBaseChange k ≫ f)
        ((relativeSectionEnrichedDiagram A).realization_precompose
          (leftFibrationBaseChangeEnriched l)))

/-- 概要：標準反復 pullback 比較を元の切断図式の全自然な指定同型へ実現する。
方針：同じ共同比較の実現同型を二つの元の底変換関手へ正規化する。
規約：実際の標準比較を保持する。使われ方：指定底変換同型の合成則の第一因子。 -/
def sectionBaseChangeCompRealizationIso {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    FunctorIso
      (leftFibrationInfinityBaseChange (l ≫ k) ≫ (relativeSectionEnrichedDiagram A).realization)
      (leftFibrationInfinityBaseChange k ≫ leftFibrationInfinityBaseChange l ≫
        (relativeSectionEnrichedDiagram A).realization) :=
  diagramIsoCongr ((relativeSectionEnrichedDiagram A).realization_precompose
    (leftFibrationBaseChangeEnriched (l ≫ k))) (sectionBaseChangeIteratedRealization k l A)
      ((sectionBaseChangeCompComparison k l A).realizationIso
        (sectionBaseChangeCompComparison_isQCatEquivalence k l A))

/-- 概要：第二段の元の底変換同型を第一段で前合成したものは元の共同比較の実現。
方針：共同実現の豊穣前合成の式と既存同型の端点正規化を使う。
規約：元の指定同型を保持する。使われ方：切断底変換の合成の中間因子。 -/
lemma relativeSectionBaseChangeRealizationIso_precomp_normalized {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    (relativeSectionBaseChangeRealizationIso l A).precomp (leftFibrationInfinityBaseChange k) =
      diagramIsoCongr (sectionBaseChangeIteratedRealization k l A)
        ((relativeSectionEnrichedDiagram (A ⋙ Over.map l)).realization_precompose
          (leftFibrationBaseChangeEnriched k))
        ((jointComparisonPrecompose (relativeSectionBaseChangeComparison l A)
          (leftFibrationBaseChangeEnriched k)).realizationIso
            (jointComparisonPrecompose_isQCatEquivalence
              (relativeSectionBaseChangeComparison l A) (leftFibrationBaseChangeEnriched k)
              (relativeSectionBaseChangeComparison_isQCatEquivalence l A))) := by
  rw [jointRealizationIso_precompose (relativeSectionBaseChangeComparison l A)
    (leftFibrationBaseChangeEnriched k) (relativeSectionBaseChangeComparison_isQCatEquivalence l A),
    diagramIsoCongr_comp, relativeSectionBaseChangeRealizationIso_normalized,
    diagramIsoCongr_precomp]
  rfl

/-- 概要：二つの元の切断底変換同型と標準反復 pullback 比較は一度の指定同型に一致する。
方針：三因子の端点移送を合成し、全共同比較の合成則を使う。
規約：元の全図式の指定同型の等式。使われ方：単体切断比較と指定分類同型への降下。 -/
lemma relativeSectionBaseChangeRealizationIso_comp {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    sectionBaseChangeCompRealizationIso k l A ≪≫
      (relativeSectionBaseChangeRealizationIso l A).precomp (leftFibrationInfinityBaseChange k) ≪≫
      relativeSectionBaseChangeRealizationIso k (A ⋙ Over.map l) =
        relativeSectionBaseChangeRealizationIso (l ≫ k) A := by
  rw [sectionBaseChangeCompRealizationIso,
    relativeSectionBaseChangeRealizationIso_precomp_normalized,
    relativeSectionBaseChangeRealizationIso_normalized k (A ⋙ Over.map l),
    ← diagramIsoCongr_trans, ← diagramIsoCongr_trans]
  change diagramIsoCongr _ _ (sectionBaseChangeCompositeRealizationIso k l A) = _
  rw [sectionBaseChangeCompositeRealizationIso_eq,
    relativeSectionBaseChangeRealizationIso_normalized]

end SerrePositivity.InfinityCategories.F2.Presentable
