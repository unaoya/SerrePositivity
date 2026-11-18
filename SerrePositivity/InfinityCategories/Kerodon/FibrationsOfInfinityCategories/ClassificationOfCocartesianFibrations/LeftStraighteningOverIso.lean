module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinityEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：底上の同型は実際の straightening の全分類図式の関手同型を与える。
方針：既存の fibration の頂点の同型を共同分類関手で送り、頂点表示を戻す。
規約：各底の対象の同型の選択ではなく、底全体の一つの関手同型を保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、S8 の同じ Hom の模型の係数移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]

/-- fibration の指定頂点の同型を、実際の底全体の分類図式の関手同型へ送る。
Kerodon Corollary 5.6.0.6（Tag 028T）、既存の共同分類関手の同型の保存則。 -/
def leftStraighteningInfinityDiagram_mapVertexIso
    (e : VertexIso (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)) :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) :=
  eqToIso (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_vertex p)) ≪≫
    VertexIso.map e (leftStraighteningInfinityMap B) ≪≫
      (eqToIso (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_vertex q))).symm

/-- 底上の指定同型を、実際の全分類図式の同じ関手同型へ送る。
Kerodon Corollary 5.6.0.6（Tag 028T）、元の射の同型を保つ係数移送の法則。 -/
def leftStraighteningInfinityDiagram_overIso [Quasicategory B]
    (e : Over.mk p ≅ Over.mk q) :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) :=
  leftStraighteningInfinityDiagram_mapVertexIso p q
    (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q e.hom.left e.hom.w
      (isPrecompositionEquivalence_of_iso ((Over.forget B).mapIso e)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
