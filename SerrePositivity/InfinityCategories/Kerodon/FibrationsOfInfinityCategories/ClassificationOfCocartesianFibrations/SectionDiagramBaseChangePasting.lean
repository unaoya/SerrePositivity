module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeRealizationComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TransposeFunctorIsoRestriction

/-!
概要：指定共同切断底変換同型の合成則を転置した図式でも保持する。
方針：既存の実現同型の合成則と、同じ指定同型の転置・制限の法則を使う。
規約：元の反復引き戻し比較と二つの指定底変換を変えない。
使われ方：Kerodon §5.6（Tag 027M）のleft fibrationの分類における
指定底変換同型の合成の、初頂点降下前の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：元の標準反復引き戻し比較を共同切断図式の指定同型へ転置する。
方針：元の実現比較を転置し、厳密な第一変数制限式で端点を正規化する。
規約：底と添字には追加の充填条件を課さない。
使われ方：二段階の指定底変換と一段階の底変換を同じ図式上で照合する。 -/
def sectionDiagramBaseChangeCompIso {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    FunctorIso
      (relativeSectionDiagramInfinity A ≫
        (pre (leftFibrationInfinityBaseChange (l ≫ k))).app SpaceInfinity.{u})
      ((relativeSectionDiagramInfinity A ≫
        (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) :=
  diagramIsoCongr
    (transposeFunctorFamily_comp (leftFibrationInfinityBaseChange (l ≫ k))
      (relativeSectionEnrichedDiagram A).realization)
    ((transposeFunctorFamily_comp (leftFibrationInfinityBaseChange k)
      (leftFibrationInfinityBaseChange l ≫ (relativeSectionEnrichedDiagram A).realization)).trans
      (congrArg (fun f ↦ f ≫ (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})
        (transposeFunctorFamily_comp (leftFibrationInfinityBaseChange l)
          (relativeSectionEnrichedDiagram A).realization)))
    (sectionBaseChangeCompRealizationIso k l A).transpose

/-- 概要：転置した二つの元の切断底変換は標準反復引き戻し比較を介して合成を保つ。
方針：指定実現同型の合成則を転置し、同じ端点移送を相殺する。
規約：全図式の指定同型自身を比較する。使われ方：指定straightening合成則の降下。 -/
lemma relativeSectionDiagramInfinityBaseChangeIso_comp {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    sectionDiagramBaseChangeCompIso k l A ≪≫
      (relativeSectionDiagramInfinityBaseChangeIso l A).postcomp
        ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) ≪≫
      relativeSectionDiagramInfinityBaseChangeIso k (A ⋙ Over.map l) =
        relativeSectionDiagramInfinityBaseChangeIso (l ≫ k) A := by
  rw [sectionDiagramBaseChangeCompIso,
    relativeSectionDiagramInfinityBaseChangeIso_normalized,
    relativeSectionDiagramInfinityBaseChangeIso_normalized,
    relativeSectionDiagramInfinityBaseChangeIso_normalized,
    diagramIsoCongr_postcomp,
    ← functorIsoTranspose_precomp, diagramIsoCongr_comp,
    ← diagramIsoCongr_trans, ← diagramIsoCongr_trans,
    ← functorIsoTranspose_trans, ← functorIsoTranspose_trans,
    relativeSectionBaseChangeRealizationIso_comp]

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
