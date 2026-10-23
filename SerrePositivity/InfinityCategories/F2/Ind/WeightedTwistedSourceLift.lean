module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedSourceBase
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEssentialExtension

/-!
概要：元の全 twisted-arrow 評価を、全添字上で同じ共同 left fibration へ降ろす。
方針：元の weighted 相対比較の前合成同値に沿って相対射を延長する。
規約：元の評価との相対同型も保持。使われ方：共同分類への一つの密度変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)
local notation "p" => leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C)
local notation "b" => weightedTwistedSourceBase F
local notation "r" => weightedRightTwistedComparison F
local notation "e" => weightedRightTwistedEvaluation F

/-- 全添字で一つの相対持ち上げと、元の全 twisted-arrow 評価との指定比較を保持する。 -/
structure WeightedTwistedSourceLift where
  map : weightedNerve (strictRightTwistedElementsDiagram F) ⟶
    weightedNerve (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C))
  over_base : map ≫ p = b
  evaluationIso : VertexIso
    (relativeFunctorVertex p (r ≫ b) (r ≫ map) (by rw [Category.assoc, over_base]))
    (relativeFunctorVertex p (r ≫ b) e (weightedRightTwistedEvaluation_over F))

/-- 元の全評価を保つ同じ共同底上の持ち上げは、追加の同値性仮定なしに存在する。 -/
lemma weightedTwistedSourceLift_nonempty [Quasicategory C] :
    Nonempty (WeightedTwistedSourceLift F) := by
  have : Quasicategory (C.op ⊗ nerve I) :=
    quasicategory_of_innerFibration (fst C.op (nerve I))
  obtain ⟨L, hL, ⟨he⟩⟩ := exists_relativeFunctorExtension_of_precompositionEquivalence
    p b r (weightedRightTwistedComparison_isPrecompositionEquivalence F) e
    (weightedRightTwistedEvaluation_over F)
  exact ⟨⟨L, hL, he⟩⟩

/-- 同じ元の共同評価を保つ、一つの全高次の持ち上げを固定する。 -/
def weightedTwistedSourceLift [Quasicategory C] : WeightedTwistedSourceLift F :=
  Classical.choice (weightedTwistedSourceLift_nonempty F)

end SerrePositivity.InfinityCategories.F2.Ind
