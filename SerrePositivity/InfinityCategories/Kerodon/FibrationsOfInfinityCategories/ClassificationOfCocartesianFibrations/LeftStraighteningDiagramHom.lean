module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
/-!
概要：元の全 straightening が同じ底上の射へ与える全図式間の射。
方針：既存の全 straightening 関手による同じ底上の射の像を使う。
規約：元の射と指定された射影を保つ。弱同値の仮定は追加しない。
使われ方：IS-W2 R03d の全関手同型を構成するための、同じ全変換の射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の全分類関手の射の像を、同じ両端の図式の射として表す。 -/
def leftStraighteningInfinityDiagramHom {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    FunctorHom (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) := by
  have h := (hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)
  change (HomotopyCategory.mk ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌)
      (leftFibrationInfinityVertex p)) ⟶
    HomotopyCategory.mk ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌)
      (leftFibrationInfinityVertex q))) at h
  rw [← leftStraighteningInfinityDiagram_vertex p, ← leftStraighteningInfinityDiagram_vertex q] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
