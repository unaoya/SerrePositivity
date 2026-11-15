module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestrictionValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationJointEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoChainTransport
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：底変換後の共同制限同型の係数評価を元の引き戻し対象の制限同型へ戻す。
方針：転置の頂点評価の既存の式と、元の実現の頂点表示を使う。
規約：図式全体の写像を比較する。
使われ方：Kerodon §5.6（Tag 027M）の指定分類底変換の三因子の端点正規化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Project.QuasicategoryAuxiliaries
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

local instance restrictionPullbackValue_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：底変換関手による前合成の後での係数評価は、同じ引き戻し対象の評価。
方針：評価の前合成則と底変換の元の頂点公式を使う。
規約：標準引き戻しを保持する。使われ方：共同制限の第三因子の係数移送。 -/
lemma leftFibrationBaseChange_evaluate {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u} ≫
        evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p) =
      evaluateFunctorAt (Y := SpaceInfinity.{u})
        (leftFibrationInfinityVertex (pullback.snd p k)) := by
  exact (evaluateFunctorAt_precomp (X := SpaceInfinity.{u})
    (leftFibrationInfinityBaseChange k) (leftFibrationInfinityVertex p)).trans
    (congrArg (fun x ↦ evaluateFunctorAt (Y := SpaceInfinity.{u}) x)
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p)))

/-- 概要：底変換を後合成した共同制限同型の同じ係数は、引き戻し対象の指定制限同型。
方針：後合成の結合則と元の係数評価の式を使う。
規約：新しい同型を選ばない。使われ方：指定底変換の第三因子の正規化。 -/
lemma leftClassificationSimplexIso_pullback_heq_joint
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (FunctorIso.postcomp
        (FunctorIso.postcomp (leftStraighteningSectionJointDiagram_restrictIso D)
          ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (leftClassificationSimplexIso (pullback.snd p k)) := by
  let R := leftStraighteningSectionJointDiagram_restrictIso D
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have hv := functorIso_postcomp_heq_of_map_eq R (leftFibrationBaseChange_evaluate p k)
  exact (functorIso_postcomp_postcomp R P evp).heq.trans
    (hv.symm.trans (leftClassificationSimplexIso_heq_joint_postcomp
      (pullback.snd p k)).symm)

private lemma isoSymm_heq {L : Type v} [Category.{w} L]
    {a b a' b' : L} (e : a ≅ b) (e' : a' ≅ b')
    (ha : a = a') (hb : b = b') (h : HEq e e') : HEq e.symm e'.symm := by
  subst a' b'
  cases eq_of_heq h
  rfl

/-- 概要：第三因子の逆制限同型の係数値も同じ引き戻し対象の逆制限同型。
方針：後合成と逆同型の交換則を同じ端点での異種等式に適用する。
規約：元の逆同型を保持する。使われ方：二段底変換の中間制限同型の消去。 -/
lemma leftClassificationSimplexIso_pullback_symm_heq_joint
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (FunctorIso.postcomp
        (FunctorIso.postcomp (leftStraighteningSectionJointDiagram_restrictIso D)
          ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})).symm
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (leftClassificationSimplexIso (pullback.snd p k)).symm := by
  let R := leftStraighteningSectionJointDiagram_restrictIso D
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
  have hf : (((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        leftStraighteningSectionJointDiagram D) ≫ P) ≫ evp =
      (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        leftStraighteningInfinityDiagram (pullback.snd p k) := by
    rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
      leftStraighteningInfinityDiagram_joint_evaluate (pullback.snd p k)]
  have hg : (transportSimplexSectionInfinity D ≫ P) ≫ evp =
      kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
          (leftFibrationObjectOf (pullback.snd p k))) := by
    rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
      transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)]
  have hs := isoSymm_heq (FunctorIso.postcomp (FunctorIso.postcomp R P) evp)
    (leftClassificationSimplexIso (pullback.snd p k))
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hf)
    (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hg)
    (leftClassificationSimplexIso_pullback_heq_joint p k)
  exact (functorIso_postcomp_symm (FunctorIso.postcomp R P) evp).heq.trans hs

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
