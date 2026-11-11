module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PostcompositionFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MixedHomVertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices

/-!
概要：元の後合成 fiber の指定頂点を、標準 Hom 比較による同じ対角頂点として読む。
方針：元の core の前合成頂点を通常の合成射へ戻し、標準比較の頂点式を使う。
規約：元の固定成分と輸送射をそのまま保持する。
使われ方：合成三角形の対角 fiber と、元の指定外ホーン fiber の境界を揃える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 0)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1)
local notation "Z" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)
local notation "f₀₁" => CategoryTheory.Functor.map
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow
local notation "k" => Equiv.symm (SimplicialCategory.homEquiv' B Z) b.down

/-- 元の後合成 fiber の指定頂点を、標準 Hom 比較で実現した対角の頂点。 -/
def cocartesianPostcompositionDiagonalVertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Z)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A Z).app (Opposite.op ⦋0⦌)
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (F.val.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).app
      (G.val.obj (ULift.up 1)))).app (Opposite.op ⦋0⦌) b.down))

/-- 同じ対角頂点は、元の輸送射と固定成分の通常の合成の coherent な辺。 -/
lemma cocartesianPostcompositionDiagonalVertex_eq :
    cocartesianPostcompositionDiagonalVertex F G b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f₀₁ ≫ k)) := by
  have hb : SimplicialCategory.homEquiv' B Z k = b.down := Equiv.apply_symm_apply _ _
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatHomVertex_pre A B Z f₀₁ k
  rw [hb] at hc
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A Z).app (Opposite.op ⦋0⦌)
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
      ((pre (show (A).obj ⟶ (B).obj from f₀₁)).app (Z).obj)).app
        (Opposite.op ⦋0⦌) b.down)) = _
  rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply]

/-- 指定された同じ対角頂点から、元の合成射の辺を厳密に回収する。 -/
lemma cocartesianPostcompositionDiagonalVertex_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (cocartesianPostcompositionDiagonalVertex F G b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f₀₁ ≫ k) := by
  rw [cocartesianPostcompositionDiagonalVertex_eq]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
