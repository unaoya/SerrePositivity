module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.StrictTransportEvaluationPrism
public import SerrePositivity.KST.Fibration.StrictTransportUnderEdge

/-! # 元の strict transport と両端 fiber 評価を結ぶ全 section 上の実 prism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ入力射に沿い、元の全 strict section を同時に評価する prism。 -/
def strictTransportEvaluationPrism {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p c ⟶ E :=
  sectionEdgePrism p (nerveMap (Under.forget c)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge f)

/-- 始点は元の strict section の同じ恒等射評価。 -/
theorem strictTransportEvaluationPrism_zero {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ strictTransportEvaluationPrism p f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) := by
  have he := sectionEdgePrism_endpoint p (nerveMap (Under.forget c))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge f) 0
  rw [strictTransportUnderEdge_zero] at he
  exact he.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportEvaluate_ambient p c).symm


/-- 終点は元の strict transport の後の、同じ終点の恒等射評価。 -/
theorem strictTransportEvaluationPrism_one {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ strictTransportEvaluationPrism p f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap p f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) := by
  have he := sectionEdgePrism_endpoint p (nerveMap (Under.forget c))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge f) 1
  rw [strictTransportUnderEdge_one] at he
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate_overPre p
    (Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection f) :
      Over.mk (nerveMap (Under.forget d)) ⟶ Over.mk (nerveMap (Under.forget c)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap p f ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (nerveMap (Under.forget d)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (nerveMap (Under.forget c))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 d)))) at ht
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.kanCocartesianUnderMap_identity_vertex] at ht
  exact he.trans (ht.symm.trans (congrArg
    (fun m => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap p f ≫ m)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportEvaluate_ambient p d).symm))


/-- 底の prism は、元の入力射そのものの定値パラメータ族。 -/
theorem strictTransportEvaluationPrism_projection
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) {c d : I} (f : c ⟶ d) :
    strictTransportEvaluationPrism p f ≫ p =
      fst (Δ[1] : SSet.{u}) _ ≫ yonedaEquiv.symm (nerve.edgeMk f).edge := by
  rw [strictTransportEvaluationPrism, sectionEdgePrism_projection,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportUnderEdge_projection]
  rfl

end SerrePositivity.KST.Fibration
