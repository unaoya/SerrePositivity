module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChangeRestrictionNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftClassificationSimplexRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NormalizedFunctorIsoComponentRestriction

/-!
概要：指定分類底変換の一対象成分の初頂点制限を、同じ共同切断比較へ戻す。
方針：指定成分の制限と、全対象の指定同型の制限を同じ評価点で比較する。
規約：元の分類底変換同型を保持する。
使われ方：Kerodon §5.6（Tag 027M）の分類の指定底変換合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：指定分類底変換の元の対象成分の制限は、同じ切断比較の転置の値。
方針：元の正規化した成分の制限則と、全対象の初頂点制限の法則を合成する。
規約：元の同型自身の異種等式。使われ方：貼り合わせ合成則の三因子の値の照合。 -/
lemma leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_heq
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))
      (functorIsoValue (straighteningBaseChangeRestrictionIso k).transpose
        (leftFibrationInfinityVertex p)) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let q := U.map (transportSimplexFirstVertexMap D)
  let P := (pre q).app SpaceInfinity.{u}
  have hp := normalizedFunctorIsoComponent_precomp_heq
    (leftStraighteningInfinityMap_baseChangeIso k) (leftFibrationInfinityVertex p)
    (leftClassificationBaseChange_sourceEq p k) (leftClassificationBaseChange_targetEq p k) q
  rw [leftClassificationBaseChange_component] at hp
  have hpv := hp.trans (functorIsoValue_eq_app
    ((leftStraighteningInfinityMap_baseChangeIso k).postcomp P)
      (leftFibrationInfinityVertex p)).symm.heq
  have hf : transposeFunctorFamily (q ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B)) =
      (leftStraighteningInfinityMap B ≫ (pre (U.map k)).app SpaceInfinity.{u}) ≫ P :=
    (transposeFunctorFamily_comp q (U.map k ≫ leftStraighteningSectionJointDiagram B)).trans
      (congrArg (fun f ↦ f ≫ P)
        (transposeFunctorFamily_comp (U.map k) (leftStraighteningSectionJointDiagram B)))
  have hg : transposeFunctorFamily (q ≫ (leftStraighteningSectionJointDiagram D ≫
      (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) =
      (leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D) ≫ P :=
    (transposeFunctorFamily_comp q (leftStraighteningSectionJointDiagram D ≫
      (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})).trans
      (congrArg (fun f ↦ f ≫ P) (transposeFunctorFamily_pre
        (leftStraighteningSectionJointDiagram D) (leftFibrationInfinityBaseChange k)))
  have hv := functorIsoValue_heq_of_heq
    ((leftStraighteningInfinityMap_baseChangeIso k).postcomp P)
    (straighteningBaseChangeRestrictionIso k).transpose hf.symm hg.symm
    (leftStraighteningInfinityMap_baseChangeIso_firstVertex_heq k) (leftFibrationInfinityVertex p)
  exact hpv.trans hv

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
