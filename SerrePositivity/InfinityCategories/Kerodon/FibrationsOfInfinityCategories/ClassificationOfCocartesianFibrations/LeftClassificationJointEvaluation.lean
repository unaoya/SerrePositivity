module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorFamilyTranspose

/-!
概要：共同分類図式と共同切断図式の同じ係数評価を元の指定図式へ戻す。
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
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：共同分類図式の同じ係数での評価は元の分類図式自身。
方針：転置の頂点評価と元の分類図式の頂点表示を比較し、頂点表示の忠実性を使う。
規約：任意の底とleft fibrationを許す。使われ方：元の制限同型の始域の表示変更。 -/
lemma leftStraighteningInfinityDiagram_joint_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    leftStraighteningSectionJointDiagram B ≫
      evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p) =
      leftStraighteningInfinityDiagram p := by
  apply functorVertex_injective
  have h := transposeFunctorFamily_vertex (leftStraighteningSectionJointDiagram B)
    (leftFibrationInfinityVertex p)
  exact h.symm.trans (leftStraighteningInfinityDiagram_vertex p).symm

/-- 概要：共同切断図式の同じ係数での評価は元のKan値切断図式全体。
方針：二重転置の厳密な式と、元の共同切断実現の頂点表示を使う。
規約：各添字の値だけに弱めない。使われ方：元の制限同型の終域の表示変更。 -/
lemma transportSimplexSectionInfinity_joint_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    transportSimplexSectionInfinity B ≫
      evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p) =
      kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p)) := by
  apply functorVertex_injective
  let R := relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)
  have h := transposeFunctorFamily_vertex (transportSimplexSectionInfinity B)
    (leftFibrationInfinityVertex p)
  have hr : transposeFunctorFamily (transportSimplexSectionInfinity B) = R.realization :=
    internalHomFlipHomEquiv_transposeFunctorFamily R.realization
  rw [hr] at h
  exact h.symm.trans (R.realization_vertex (leftFibrationObjectOf p))

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
