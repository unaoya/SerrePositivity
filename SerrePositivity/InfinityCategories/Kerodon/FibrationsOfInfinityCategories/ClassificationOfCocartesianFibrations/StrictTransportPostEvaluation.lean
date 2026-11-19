module
public import SerrePositivity.KST.Fibration.StrictTransportPostToLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointFiberEvaluation

/-! # 同じ全 strict transport 比較の、元の恒等射評価との厳密な可換性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Fibration

/-- 左 fibration への同じ後合成は、元の section の各頂点評価と厳密に可換。 -/
theorem sectionPostToLeftFibration_evaluate {A E T B : SSet.{u}}
    (p : E ⟶ B) (q : T ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (a : A ⟶ B) (v : A _⦋0⦌) :
    sectionPostToLeftFibration p q f hf a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate q a v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p a v ≫ f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate
  rw [← Category.assoc, sectionPostToLeftFibration_ι, Category.assoc,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p q f hf a), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost_ι,
    Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.evaluateFunctorAt_post, ← Category.assoc]
  simp only [Category.assoc]

/-- strict transport の同じ恒等射評価は、元の全空間への後合成を回収する。 -/
theorem strictTransportPostToLeftFibration_evaluate_ambient
    {I : Type u} [Category.{u} I] {E T : SSet.{u}}
    (p : E ⟶ nerve I) (q : T ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (c : I) :
    (strictTransportPostToLeftFibration p q f hf).app c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate q c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) ≫ f := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportEvaluate_ambient, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportEvaluate_ambient]
  exact sectionPostToLeftFibration_evaluate p q f hf _ _

/-- 同じ評価は fiber 内でも、元の底上の関手から誘導した実 fiber 写像そのもの。 -/
theorem strictTransportPostToLeftFibration_evaluate
    {I : Type u} [Category.{u} I] {E T : SSet.{u}}
    (p : E ⟶ nerve I) (q : T ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (c : I) :
    (strictTransportPostToLeftFibration p q f hf).app c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate q c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
  rw [Category.assoc, strictTransportPostToLeftFibration_evaluate_ambient,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

end SerrePositivity.KST.Fibration
