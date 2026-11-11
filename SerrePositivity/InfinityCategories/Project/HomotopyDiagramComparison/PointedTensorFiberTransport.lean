module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedTensorCoefficient
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.TensorHomotopyEquivalence

/-!
概要：元の二射影の coherent 辺に沿う普遍 fiber の輸送の対は同値。
方針：同じ係数同型と両側の標準比較を、両射影の輸送との可換性で結ぶ。
規約：二つの元の射影辺を保持。使われ方：点ごとの積図式の全空間比較の fiber 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan

/-- 元の fst・snd の coherent 辺に沿う普遍輸送を組にする。 -/
def pointedTensorFiberTransport (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K) ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex L) :=
  lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ K from fst K.obj L.obj)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ L from snd K.obj L.obj)))

/-- 同じ係数同型から fiber の積への比較は、元の両射影の輸送の対と可換。 -/
def pointedTensorFiberTransportComparisonIso (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTensorCoefficientIso K L).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison K ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison L))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L) ≫
        pointedTensorFiberTransport K L) := by
  let a : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ K := fst K.obj L.obj
  let b : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ L := snd K.obj L.obj
  let c := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L)
  let f := (SSet.uliftFunctor.{u + 1, u}).map
    (SSet.opFunctor.map (eHomWhiskerLeft SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject a))
  let g := (SSet.uliftFunctor.{u + 1, u}).map
    (SSet.opFunctor.map (eHomWhiskerLeft SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject b))
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b)
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.pairedSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison_transportIso a).simplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison_transportIso b).simplicialHomotopy
  have h₀ : lift (f ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison K) (g ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison L) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTensorCoefficientIso K L).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison K ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison L) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc, tensorHom_fst, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTensorCoefficientIso_fst]
    · rw [lift_snd, Category.assoc, tensorHom_snd, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTensorCoefficientIso_snd]
  have h₁ : lift (c ≫ p) (c ≫ q) = c ≫ pointedTensorFiberTransport K L := by
    rw [pointedTensorFiberTransport, comp_lift]
  change SSet.Homotopy
    (lift (f ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison K) (g ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison L))
    (lift (c ≫ p) (c ≫ q)) at H
  rw [h₀, h₁] at H
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H

/-- 元の二射影の普遍 fiber 輸送の対は同じ実際の射について同値。 -/
lemma pointedTensorFiberTransport_isQCatEquivalence (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pointedTensorFiberTransport K L) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTensorCoefficientIso K L)).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.tensor_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison_isQCatEquivalence K)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison_isQCatEquivalence L))
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedCoherentFiberComparison_isQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L)).cancel_left
    (h.ofFunctorIso (pointedTensorFiberTransportComparisonIso K L))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
