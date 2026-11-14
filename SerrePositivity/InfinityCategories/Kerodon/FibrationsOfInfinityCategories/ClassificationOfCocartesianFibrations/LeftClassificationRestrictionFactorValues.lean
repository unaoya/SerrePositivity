module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestrictionValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationJointEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition

/-!
概要：共同制限同型の前合成と係数評価を交換し、元の指定制限同型へ戻す。
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
open Project.QuasicategoryAuxiliaries
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：共同制限同型の前合成後の係数評価は、元の指定制限同型の前合成。
方針：前後合成の交換則と同じ制限同型の係数評価の法則を使う。
規約：元の同型の値を保持する。使われ方：指定底変換の第一因子の正規化。 -/
lemma leftClassificationSimplexIso_precomp_heq_joint
    {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {K : SSet.{u + 1}}
    (t : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B))) :
    HEq (FunctorIso.postcomp
        ((leftStraighteningSectionJointDiagram_restrictIso B).precomp t)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (FunctorIso.precomp (leftClassificationSimplexIso p) t) := by
  let R := leftStraighteningSectionJointDiagram_restrictIso B
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have hf : ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) ≫ evp =
      (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p := by
    rw [Category.assoc, leftStraighteningInfinityDiagram_joint_evaluate p]
  have hg := transportSimplexSectionInfinity_joint_evaluate p
  have hv := functorIso_precomp_heq_of_heq (FunctorIso.postcomp R evp)
    (leftClassificationSimplexIso p) hf hg
    (leftClassificationSimplexIso_heq_joint_postcomp p) t
  exact (functorIso_precomp_postcomp R t evp).heq.trans hv.symm

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
