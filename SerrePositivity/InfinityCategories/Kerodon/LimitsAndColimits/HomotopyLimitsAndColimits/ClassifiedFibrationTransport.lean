module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningIsoHom

/-!
概要：指定された全分類同型の同じ変換を、元の射影の共通の復元への実写像で保持する。
方針：元の復元射に、指定二胞体を回収する既存のunstraightening写像を合成する。
規約：IS-W2 R03bの証明分割。底上の同値だけで指定変換の代用にしない。
使われ方：切断比較の三角形と元の指定BK点の評価の追跡。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

/-- 同じ元の分類同型の変換を使う、共通の復元への実写像。 -/
def classifiedFibrationTransport :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram q) :=
  leftStraighteningInfinityReconstruction p ≫ smallUnstraighteningFunctorHom η.hom

/-- 同じ実写像は底の元の射影を厳密に保つ。 -/
theorem classifiedFibrationTransport_projection :
    classifiedFibrationTransport p q η ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) = p := by
  rw [classifiedFibrationTransport, Category.assoc, smallUnstraighteningFunctorHom_projection,
    leftStraighteningInfinityReconstruction_projection]

/-- 同じ指定変換による実写像自身が前合成同値。 -/
theorem classifiedFibrationTransport_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (classifiedFibrationTransport p q η) :=
  (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).comp
    (smallUnstraighteningFunctorHom_isPrecompositionEquivalence η.hom)

/-- 使用する代表辺の類は、元の指定分類同型の変換そのもの。 -/
theorem classifiedFibrationTransport_edge_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (smallUnstraighteningHomEdge η.hom).toTruncated = η.hom :=
  smallUnstraighteningHomEdge_hom η.hom

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
