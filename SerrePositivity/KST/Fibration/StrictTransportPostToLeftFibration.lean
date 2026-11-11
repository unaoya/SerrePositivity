module
public import SerrePositivity.KST.Fibration.SectionPostToLeftFibration
public import SerrePositivity.KST.Fibration.CocartesianKanDiagram
public import SerrePositivity.KST.Fibration.StrictTransportEvaluationPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-! # 左 fibration への同じ評価関手による strict transport 図式全体の自然変換 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E T : SSet.{u}}
  (p : E ⟶ nerve I) (q : T ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
  (f : E ⟶ T) (hf : f ≫ q = p)

/-- 元の同じ底上の評価関手は、全 undercategory 上の strict transport 図式を自然に結ぶ。 -/
def strictTransportPostToLeftFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram q where
  app c := sectionPostToLeftFibration p q f hf (nerveMap (Under.forget c))
  naturality {c d} a := by
    let j : Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)) :=
      Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection a)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p j ≫
        sectionPostToLeftFibration p q f hf (nerveMap (Under.forget d)) =
      sectionPostToLeftFibration p q f hf (nerveMap (Under.forget c)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre q j
    exact (sectionPostToLeftFibration_overPre p q f hf j).symm

/-- 関手的な同じ Kan 置換は、元の図式全体の自然変換を保つ。 -/
def strictKanTransportPostToLeftFibration : cocartesianKanDiagram p ⟶ cocartesianKanDiagram q :=
  Functor.whiskerRight (strictTransportPostToLeftFibration p q f hf) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion

/-- 同じ自然変換を全単体の coherent 図式間の辺として保持する。 -/
def strictKanTransportPostToLeftFibrationEdge :
    Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (cocartesianKanCoherentDiagram p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (cocartesianKanCoherentDiagram q)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge
    (F := ⟨cocartesianKanDiagram p, trivial⟩) (G := ⟨cocartesianKanDiagram q, trivial⟩)
    (Functor.whiskerRight (strictKanTransportPostToLeftFibration p q f hf) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)

end SerrePositivity.KST.Fibration
