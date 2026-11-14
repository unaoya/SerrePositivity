module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsTriangle
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation

/-!
概要：指定分類変換による全切断の三角形を、元の同じ底の各fiberで評価する。
方針：元の全三角形を同じfiber評価で後合成し、後合成と評価の厳密な自然性を使う。
規約：IS-W2 R02〜R03の評価・合成則。零単体だけに弱めない。
使われ方：元のBK点の像からnative錐の同じ脚のfiber比較への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
attribute [local instance] simplicialSections_kanComplex
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

/-- 同じ元の全切断三角形は、各fiberでの同じ評価とも可換。 -/
def classifiedLeftFibrationSectionsEquivalence_fiber_triangle (b : B _⦋0⦌) :
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsFiberEvaluation q b ≫
          vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
            (leftStraighteningInfinityReconstruction_projection q) b)
      (simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b) := by
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  have h := FunctorIso.postcomp (classifiedLeftFibrationSectionsEquivalence_triangle p q η)
    (simplicialSectionsFiberEvaluation r b)
  have hq := simplicialSectionsFiberEvaluation_naturality q r
    (leftStraighteningInfinityReconstruction q)
    (leftStraighteningInfinityReconstruction_projection q) b
  have hp := simplicialSectionsFiberEvaluation_naturality p r
    (classifiedFibrationTransport p q η) (classifiedFibrationTransport_projection p q η) b
  rw [Category.assoc, hq, hp] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
