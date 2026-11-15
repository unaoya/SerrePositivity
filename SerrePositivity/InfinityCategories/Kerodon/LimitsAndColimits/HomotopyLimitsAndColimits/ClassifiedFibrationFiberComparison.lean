module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsFiberTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection

/-!
概要：元の全分類同型による切断比較を、元の二つのfiberの同値と両立させる。
方針：共通の復元への二本のfiber同値を合成し、元の全切断三角形を余単位で戻す。
規約：IS-W2 R03c。元の切断比較との同じ全四角形を保持する。
使われ方：同じBK点から元のnative錐の脚のfiber比較へ戻る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open scoped Simplicial
attribute [local instance] simplicialSections_kanComplex vertexFiber_kanComplex_of_leftFibration
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

/-- 共通の復元への同じ二本のfiber同値から、元のfiber間へ戻る。 -/
def classifiedFibrationFiberEquivalence (b : B _⦋0⦌) :
    QCatEquivalence (vertexFiber p b) (vertexFiber q b) := by
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  let f := (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p r
    (classifiedFibrationTransport p q η) (classifiedFibrationTransport_projection p q η)
      (classifiedFibrationTransport_isPrecompositionEquivalence p q η) b).choose
  let g := (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence q r
    (leftStraighteningInfinityReconstruction q) (leftStraighteningInfinityReconstruction_projection q)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q) b).choose
  exact f.trans g.symm

/-- 同じ元の全切断比較のfiberでの作用は、上の同じfiber同値と全関手同型で両立。 -/
def classifiedFibrationFiberEquivalence_sectionsIso (b : B _⦋0⦌) :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsFiberEvaluation q b)
      (simplicialSectionsFiberEvaluation p b ≫ (classifiedFibrationFiberEquivalence p q η b).hom) := by
  let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
  let f := (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p r
    (classifiedFibrationTransport p q η) (classifiedFibrationTransport_projection p q η)
      (classifiedFibrationTransport_isPrecompositionEquivalence p q η) b).choose
  let g := (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence q r
    (leftStraighteningInfinityReconstruction q) (leftStraighteningInfinityReconstruction_projection q)
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q) b).choose
  let a := (classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
    simplicialSectionsFiberEvaluation q b
  have h := FunctorIso.postcomp (classifiedLeftFibrationSectionsEquivalence_fiber_triangle p q η b)
    g.inv
  have hfMap : f.hom = vertexFiberMap p r (classifiedFibrationTransport p q η)
      (classifiedFibrationTransport_projection p q η) b := rfl
  have hgMap : g.hom = vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
      (leftStraighteningInfinityReconstruction_projection q) b := rfl
  have h' : FunctorIso ((a ≫ g.hom) ≫ g.inv)
      ((simplicialSectionsFiberEvaluation p b ≫ f.hom) ≫ g.inv) := by
    simpa only [a, Category.assoc, hfMap, hgMap] using h
  have hg : FunctorIso ((a ≫ g.hom) ≫ g.inv) a := by
    simpa only [Category.assoc, Category.comp_id] using FunctorIso.precomp g.homInvIso a
  change FunctorIso a ((simplicialSectionsFiberEvaluation p b ≫ f.hom) ≫ g.inv)
  exact hg.symm.trans h'

/-- 全分類比較から、元の切断比較と同じfiber四角形を持つ同値を得る。 -/
theorem exists_classifiedFibrationFiberComparison (b : B _⦋0⦌) :
    ∃ e : QCatEquivalence (vertexFiber p b) (vertexFiber q b),
      Nonempty (FunctorIso
        ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
          simplicialSectionsFiberEvaluation q b)
        (simplicialSectionsFiberEvaluation p b ≫ e.hom)) :=
  ⟨classifiedFibrationFiberEquivalence p q η b,
    ⟨classifiedFibrationFiberEquivalence_sectionsIso p q η b⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
