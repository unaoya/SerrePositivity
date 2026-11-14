module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SectionShapeColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SectionShapeFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSkeletonColimit

/-!
概要：任意の coherent な図式の切断空間を、全ての相対骨格の切断空間の塔の極限で表す。
方針：既存の底上の骨格列の余極限へ、切断の全パラメータの貼り合わせを適用する。
規約：骨格の基準部分は任意の単射でよく、通常の圏の strict 図式へ制限しない。
使われ方：γ3c の一般の coherent 図式の境界整合性と無限段階の処理。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra SSet.relativeCellComplexOfMono
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
noncomputable section
variable {A K E X : SSet.{u}} (q : E ⟶ X) (i : A ⟶ K) [Mono i] (p : K ⟶ X)

/-- 相対骨格上の切断空間と、その全単体での制限からなる塔。 -/
def skeletalSectionDiagram : ℕᵒᵖ ⥤ SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonDiagram i p).op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverFunctor q

/-- 元の図式の切断空間から全ての骨格上の切断空間への制限の錐。 -/
def skeletalSectionCone : Cone (skeletalSectionDiagram q i p) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverColimitCone q _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonCocone i p)

/-- 全体の切断空間は、相対骨格上の切断空間の塔の厳密な極限である。 -/
def skeletalSectionCone_isLimit : IsLimit (skeletalSectionCone q i p) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverColimitCone_isLimit q _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonCocone_isColimit i p)

/-- 切断の塔の各段階は、指定した相対骨格への図式の制限の相対関手空間。 -/
lemma skeletalSectionDiagram_obj (n : ℕ) :
    (skeletalSectionDiagram q i p).obj (Opposite.op n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q ((skeletonOfMono i n).ι ≫ p) := rfl

/-- left fibration の切断の塔の各段階は Kan 複体。 -/
instance skeletalSectionDiagram_obj_kanComplex [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (n : ℕᵒᵖ) :
    KanComplex ((skeletalSectionDiagram q i p).obj n) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonDiagram i p).obj n.unop).hom))

/-- 隣り合う骨格の間の制限は Kan fibration。 -/
lemma skeletalSectionDiagram_map_fibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (n : ℕ) :
    Fibration ((skeletalSectionDiagram q i p).map (homOfLE (Nat.le_succ n)).op) := by
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinSkeletonDiagram i p).map (homOfLE (Nat.le_succ n))
  have : Mono f.left := inferInstanceAs (Mono (r i n))
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverPre_fibration q f

end
end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
