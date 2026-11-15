module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHomArrow
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBasesEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationArrow

/-!
概要：元の全図式の同じ射を、元の指定評価同型と同じfiber評価へ照合する。
方針：同じ評価関手の像を正規化し、元の全評価同型の自然性へ同じ辺を代入する。
規約：射も評価同型も選び直さず、任意の底上の射を扱う。
使われ方：同じnative全比較の指定単位の評価。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の全図式の射の同じ点での評価は、同じ全straighteningと同じ評価の像のArrow。 -/
lemma leftStraighteningInfinityDiagramHom_evaluate_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
        ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated))) := by
  have h := congrArg (fun z : Arrow (HomotopyCategory
      ((ihom ((SSet.uliftFunctor.{u+1,u}).obj B)).obj SpaceInfinity.{u})) =>
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
      z.hom)) (leftStraighteningInfinityDiagramHom_arrow p q f hf)
  simp only [Arrow.mk_hom] at h
  exact (functorHomEvaluate_arrow _ _).trans h

/-- 元の指定評価同型の全自然性を、同じ底上の射の同じ分類像へ適用する。 -/
lemma leftStraighteningInfinityMap_fiberEvaluate_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk ((hoFunctor.map
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) =
      Arrow.mk (((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex p)).hom ≫
        (hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) ≫
        ((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex q)).inv) := by
  exact congrArg Arrow.mk (CategoryTheory.NatIso.naturality_2 (leftStraighteningInfinityMap_evaluateIso b).toNatIso
    (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)).symm

/-- 元の全図式の射の評価は、同じ指定評価同型と同じfiber評価の射の像で与えられる。 -/
lemma leftStraighteningInfinityDiagramHom_fiber_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk (((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex p)).hom ≫
        (hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) ≫
        ((leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex q)).inv) := by
  have hcomp := congrArg (fun k : hoFunctor.obj (LeftFibrationInfinity B) ⟶
      hoFunctor.obj SpaceInfinity.{u} => Arrow.mk (k.toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)))
    (hoFunctor.map_comp (leftStraighteningInfinityMap B)
      (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b)))
  change Arrow.mk ((hoFunctor.map
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) =
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
      ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated))) at hcomp
  exact (leftStraighteningInfinityDiagramHom_evaluate_arrow p q f hf b).trans
    (hcomp.symm.trans (leftStraighteningInfinityMap_fiberEvaluate_arrow p q f hf b))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
