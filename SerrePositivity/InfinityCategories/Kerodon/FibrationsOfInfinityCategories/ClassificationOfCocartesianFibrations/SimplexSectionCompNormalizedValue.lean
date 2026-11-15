module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCompValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationRestrictionPullbackValue

/-!
概要：同じ全単体補正因子の係数を、標準引き戻し対象の端点へ正規化する。
方針：係数評価と端点移送の既存の法則を合成する。
規約：同じ指定同型そのものの等式。
使われ方：Kerodon §5.6（Tag 027M）の補正因子の分類像との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance simplexCompNormalizedValue_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：正規化した同じ補正因子の値は、元のKan値実現比較の同じ値。
方針：二つの端点移送を消去する。規約：同型を選び直さない。
使われ方：標準逆引き戻し射の分類との既存の自然性の式へ接続する。 -/
lemma simplexSectionCompIso_value_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    diagramIsoCongr
      (by
        rw [Category.assoc, leftFibrationBaseChange_evaluate p (l ≫ k),
          transportSimplexSectionInfinity_joint_evaluate q₀]
        rfl)
      (by
        rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
          Category.assoc, leftFibrationBaseChange_evaluate (pullback.snd p k) l,
          transportSimplexSectionInfinity_joint_evaluate q₁]
        rfl)
      (FunctorIso.postcomp (simplexSectionCompIso k l) evp) =
    kanEnrichedRealizationValueIso
      (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
      (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
      (leftFibrationObjectOf p) := by
  dsimp only
  apply eq_of_heq
  exact (diagramIsoCongr_heq _ _ _).trans (simplexSectionCompIso_value_heq p k l)

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
