module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SectionShapeOverDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletalConeSections

/-!
概要：coherent 図式の相対骨格の一段を、境界と単体の切断空間の極限として計算する。
方針：Mathlib の非退化単体のセル付加の押し出しに、底上の切断の貼り合わせを適用する。
規約：セルの attaching map と元の図式を保ち、零次元・空のセル族も含める。
使われ方：任意の coherent な図式の余極限構成の後続段階での境界の整合性。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
noncomputable section
variable {A K E X : SSet.{u}} (i : A ⟶ K) [Mono i] (p : K ⟶ X)

/-- 相対骨格のセル付加を、境界の和と単体の和からなる余錐として表示する。 -/
def skeletalCellShapeCocone (n : ℕ) : PushoutCocone (t i n) (l i n) :=
  PushoutCocone.mk (r i n) (b i n) (w i n)

/-- セル付加の形状の余錐は、通常の単体集合の押し出しである。 -/
def skeletalCellShapeCocone_isColimit (n : ℕ) : IsColimit (skeletalCellShapeCocone i n) :=
  (isPushout i n).isColimit

/-- 元の coherent 図式を保った、境界と単体のセル付加の底上の図式。 -/
def skeletalCellOverDiagram (n : ℕ) : WalkingSpan ⥤ Over X :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sectionShapeOverDiagram (skeletalCellShapeCocone i n) ((skeletonOfMono i (n + 1)).ι ≫ p)

/-- 一段大きい骨格上の切断から、元の骨格と付加セルの境界付きの切断への制限。 -/
def skeletalCellSectionCone (q : E ⟶ X) (n : ℕ) :
    Cone ((skeletalCellOverDiagram i p n).op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverFunctor q) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverColimitCone q _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sectionShapeOverCocone (skeletalCellShapeCocone i n)
    ((skeletonOfMono i (n + 1)).ι ≫ p))

/-- 後続骨格上の切断空間は、元の骨格と付加セルの境界付きの切断空間の極限。 -/
def skeletalCellSectionCone_isLimit (q : E ⟶ X) (n : ℕ) :
    IsLimit (skeletalCellSectionCone i p q n) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sectionShapeOverCone_isLimit _ _ q (skeletalCellShapeCocone_isColimit i n)

end
end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
