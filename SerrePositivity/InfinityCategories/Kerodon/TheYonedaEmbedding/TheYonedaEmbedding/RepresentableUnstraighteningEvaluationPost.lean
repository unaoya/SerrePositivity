module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluationPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeBaseChangeComposition

/-!
概要：表現可能 unstraightening の元の恒等錐での評価は、標的の同じ底上の射に自然。
方針：相対前後合成の可換性、相対評価の自然性、fiberの端点表示変更を順に使う。
規約：元の恒等錐と選択された比較射を保持する。
使われ方：G14 の Yoneda 評価の標的自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 元の恒等錐による表現可能評価は、標的の射が誘導するfiberの射と厳密に可換。 -/
lemma representableUnstraighteningEvaluation_post {E F C : SSet.{u}} [Quasicategory C]
    (p : E ⟶ C.op) (q : F ⟶ C.op) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (y : C _⦋0⦌) :
    relativeFunctorPost p q f hf (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) ≫
      representableUnstraighteningEvaluation q y =
    representableUnstraighteningEvaluation p y ≫ vertexFiberMap p q f hf (SSet.opObjEquiv.symm y) := by
  have ht {a b : C.op _⦋0⦌} (hab : a = b) :
      vertexFiberMap p q f hf a ≫ eqToHom (congrArg (vertexFiber q) hab) =
      eqToHom (congrArg (vertexFiber p) hab) ≫ vertexFiberMap p q f hf b := by
    subst b
    simp
  simp only [representableUnstraighteningEvaluation, Category.assoc]
  rw [← Category.assoc]
  erw [← relativeFunctorPost_overPre]
  rw [Category.assoc]
  rw [← Category.assoc (relativeFunctorPost p q f hf _)]
  dsimp only [Over.mk, Over.hom, CostructuredArrow.mk]
  erw [relativeFunctorEvaluate_post]
  rw [Category.assoc, ht]
  exact SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
