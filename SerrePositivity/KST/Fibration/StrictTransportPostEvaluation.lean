module
public import SerrePositivity.KST.Fibration.StrictTransportPostToLeftFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningPointFiberEvaluation

/-! # 同じ全 strict transport 比較の、元の恒等射評価との厳密な可換性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration

/-- 左 fibration への同じ後合成は、元の section の各頂点評価と厳密に可換。 -/
theorem sectionPostToLeftFibration_evaluate {A E T B : SSet.{u}}
    (p : E ⟶ B) (q : T ⟶ B) [LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (a : A ⟶ B) (v : A _⦋0⦌) :
    sectionPostToLeftFibration p q f hf a ≫ cocartesianSectionEvaluate q a v =
      cocartesianSectionEvaluate p a v ≫ f := by
  unfold cocartesianSectionEvaluate
  rw [← Category.assoc, sectionPostToLeftFibration_ι, Category.assoc,
    ← Category.assoc (relativeFunctorPost p q f hf a), relativeFunctorPost_ι,
    Category.assoc, Category.assoc, evaluateFunctorAt_post, ← Category.assoc]
  simp only [Category.assoc]

/-- strict transport の同じ恒等射評価は、元の全空間への後合成を回収する。 -/
theorem strictTransportPostToLeftFibration_evaluate_ambient
    {I : Type u} [Category.{u} I] {E T : SSet.{u}}
    (p : E ⟶ nerve I) (q : T ⟶ nerve I) [LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (c : I) :
    (strictTransportPostToLeftFibration p q f hf).app c ≫
      SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate q c ≫ vertexFiberι q (nerveVertex c) =
      SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c) ≫ f := by
  rw [strictTransportEvaluate_ambient, ← Category.assoc,
    strictTransportEvaluate_ambient]
  exact sectionPostToLeftFibration_evaluate p q f hf _ _

/-- 同じ評価は fiber 内でも、元の底上の関手から誘導した実 fiber 写像そのもの。 -/
theorem strictTransportPostToLeftFibration_evaluate
    {I : Type u} [Category.{u} I] {E T : SSet.{u}}
    (p : E ⟶ nerve I) (q : T ⟶ nerve I) [LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (c : I) :
    (strictTransportPostToLeftFibration p q f hf).app c ≫
      SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate q c =
      SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c ≫ vertexFiberMap p q f hf (nerveVertex c) := by
  apply vertexFiber_hom_ext q (nerveVertex c)
  rw [Category.assoc, strictTransportPostToLeftFibration_evaluate_ambient,
    Category.assoc, vertexFiberMap_ι]

end SerrePositivity.KST.Fibration
