module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitTransport

/-!
概要：同じ底の同型な分類図式は、全空間上の同じ係数図式の極限の存在を保つ。
方針：既存の二つの復元比較と、小さい unstraightening の同型の比較で制限する。
規約：分類図式は全底上の一つの関手同型で比較する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Definition 7.3.1.2（Tag 02Y9）、
S8 の固定 Yoneda の右 Kan 局所図式の係数移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B X : SSet.{u}} [Quasicategory B] [Quasicategory X]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]

/-- 全分類図式の指定同型で、底から来る同じ係数の極限の存在を移す。
Kerodon Corollary 5.6.0.6（Tag 028T）、既存の復元比較と同型比較の係数移送則。 -/
lemma hasLimit_iff_of_leftStraighteningIso
    (e : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))
    (O : B ⟶ X) : HasLimit (p ≫ O) ↔ HasLimit (q ≫ O) := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  letI : Quasicategory F := quasicategory_of_innerFibration q
  have hp : HasLimit (p ≫ O) ↔
      HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O) := by
    have hh := hasLimit_iff_equivalentRestriction
      (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O)
    simpa only [← Category.assoc, leftStraighteningInfinityReconstruction_projection] using hh.symm
  have hq : HasLimit (q ≫ O) ↔
      HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O) := by
    have hh := hasLimit_iff_equivalentRestriction
      (leftStraighteningInfinityReconstruction q)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q).isQCatEquivalence
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O)
    simpa only [← Category.assoc, leftStraighteningInfinityReconstruction_projection] using hh.symm
  have hm :
      HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O) ↔
      HasLimit (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O) := by
    have hh := hasLimit_iff_equivalentRestriction
      (smallLeftUnstraighteningComparisonOfFunctorIso e)
      (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence e).isQCatEquivalence
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) ≫ O)
    simpa only [← Category.assoc, smallLeftUnstraighteningComparisonOfFunctorIso_projection] using hh.symm
  exact hp.trans (hm.trans hq.symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
