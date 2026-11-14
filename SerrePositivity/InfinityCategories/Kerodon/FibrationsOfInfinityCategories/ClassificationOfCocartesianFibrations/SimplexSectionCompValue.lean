module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionComposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionBaseChangeCompValueNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra

/-!
概要：全単体の指定反復引き戻し比較の係数を、同じ比較の元の実現値へ戻す。
方針：転置の頂点評価の既存の式と、元の実現の頂点表示を使う。
規約：図式全体の写像を比較する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の三因子の端点正規化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Project.QuasicategoryAuxiliaries
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

private lemma diagramIsoCongr_postcomp_heq {A X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g')
    (e : FunctorIso f g) (q : X ⟶ Y) :
    HEq (FunctorIso.postcomp (diagramIsoCongr hf hg e) q) (FunctorIso.postcomp e q) :=
  functorIso_postcomp_heq_of_heq e (diagramIsoCongr hf hg e) hf hg
    (diagramIsoCongr_heq hf hg e) q

/-- 概要：全単体の指定反復引き戻し比較の同じ係数は、元のKan値実現比較の値。
方針：二つの端点正規化を消去し、同じ転置の評価の法則を使う。
規約：元の標準比較を保持する。使われ方：指定底変換の合成則の補正因子の分類。
対応：Kerodon §5.6（Tag 027M）の既存分類構成の係数移送。 -/
lemma simplexSectionCompIso_value_heq {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (FunctorIso.postcomp (simplexSectionCompIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (kanEnrichedRealizationValueIso
        (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
        (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
        (leftFibrationObjectOf p)) := by
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have h₀ : HEq (FunctorIso.postcomp (simplexSectionCompIso k l) evp)
      (FunctorIso.postcomp
        (sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T)) evp) := by
    unfold simplexSectionCompIso
    exact diagramIsoCongr_postcomp_heq _ _ _ _
  have h₁ : HEq (FunctorIso.postcomp
        (sectionDiagramBaseChangeCompIso k l (transportSimplexDomainFunctor T)) evp)
      (FunctorIso.postcomp
        (sectionBaseChangeCompRealizationIso k l (transportSimplexDomainFunctor T)).transpose
        evp) := by
    unfold sectionDiagramBaseChangeCompIso
    exact diagramIsoCongr_postcomp_heq _ _ _ _
  have h₂ := functorIso_transpose_postcomp_heq_value
    (sectionBaseChangeCompRealizationIso k l (transportSimplexDomainFunctor T))
    (leftFibrationInfinityVertex p)
  have h₃ := sectionBaseChangeCompRealizationIso_value_heq p k l
    (transportSimplexDomainFunctor T)
  exact h₀.trans (h₁.trans (h₂.trans h₃))

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
