module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientValues
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientPasting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionBaseChangeFactorValues

/-!
概要：同じ係数貼り合わせの因子を、元の対象別係数値とその前合成で表す。
方針：既存の因子評価の法則と、同じ端点への正規化を使う。
規約：元の比較の係数値を変えない。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の合成則。
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
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance coefficientComposition_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：第一因子を正規化すると、元の引き戻し対象の指定係数底変換になる。
方針：同じ係数評価の異種等式を正規化する。
規約：標準引き戻しの係数。使われ方：中間制限同型の相殺。 -/
lemma simplexSectionFirstCoefficient_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    diagramIsoCongr
      (f' := simplexSectionValue (pullback.snd (pullback.snd p k) l))
      (g' := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        simplexSectionValue (pullback.snd p k))
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd (pullback.snd p k) l)])
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (FunctorIso.postcomp (simplexSectionFirstIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) =
      simplexSectionBaseChangeCoefficient (pullback.snd p k) l := by
  apply eq_of_heq
  exact (diagramIsoCongr_heq _ _ _).trans
    ((simplexSectionFirstIso_value_heq p k l).trans
      (simplexSectionBaseChangeCoefficient_heq (pullback.snd p k) l).symm)

/-- 概要：第二因子の正規化は元の指定係数底変換の添字前合成。
方針：同じ前合成を係数評価の異種等式に作用させる。
規約：元の前合成。使われ方：二段の底変換の同じ因子の相殺。 -/
lemma simplexSectionSecondCoefficient_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let t := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))
    let s := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (f' := t ≫ simplexSectionValue (pullback.snd p k))
      (g' := t ≫ (s ≫ simplexSectionValue p))
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (by rw [Category.assoc, Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (simplexSectionSecondIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) =
      (simplexSectionBaseChangeCoefficient p k).precomp t := by
  dsimp only
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have hf : (transportSimplexSectionInfinity D ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) ≫ evp =
      simplexSectionValue (pullback.snd p k) := by
    rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
      transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)]
  have hg : ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B) ≫ evp =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        simplexSectionValue p := by
    rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p]
  have hv := functorIso_precomp_heq_of_heq
    (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k) evp)
    (simplexSectionBaseChangeCoefficient p k) hf hg (simplexSectionBaseChangeCoefficient_heq p k)
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)))
  exact eq_of_heq ((diagramIsoCongr_heq _ _ _).trans
    ((simplexSectionSecondIso_value p k l).heq.trans hv.symm))

/-- 概要：元の対象別係数底変換は標準反復引き戻し比較の同じ係数値を介して合成する。
方針：四端点での貼り合わせの二因子を、元の係数値の式へ戻す。
規約：全図式の同じ同型の異種等式。使われ方：元の分類底変換の共役の相殺。 -/
lemma simplexSectionBaseChangeCoefficient_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (simplexSectionCompositeCoefficient p k l ≪≫
        simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
        (simplexSectionBaseChangeCoefficient p k).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))))
      (simplexSectionBaseChangeCoefficient p (l ≫ k)) := by
  have h := simplexSectionCoefficient_pasting p k l
  dsimp only at h
  simp only [simplexSectionCompIso_value_normalized,
    simplexSectionFirstCoefficient_normalized, simplexSectionSecondCoefficient_normalized] at h
  simpa only [simplexSectionCompositeCoefficient, simplexSectionBaseChangeCoefficient,
    simplexSectionValue] using h

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
