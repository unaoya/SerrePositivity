module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition

/-!
概要：相対関手の頂点評価と、同じ底上の標的の射による後合成の可換性。
方針：標的fiberの包含後に、元の内部 Hom の評価の自然性を使う。
規約：任意の単体集合と頂点に対する厳密な等式。
使われ方：G14 の Yoneda の恒等錐での評価を標的自然性へ結ぶ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 相対評価は、同じ標的の射がfiberに誘導する射と厳密に可換。 -/
lemma relativeFunctorEvaluate_post {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (a : A ⟶ B) (v : A _⦋0⦌) :
    relativeFunctorPost p q f hf a ≫ relativeFunctorEvaluate q a v =
      relativeFunctorEvaluate p a v ≫ vertexFiberMap p q f hf (a.app (Opposite.op ⦋0⦌) v) := by
  apply vertexFiber_hom_ext q (a.app (Opposite.op ⦋0⦌) v)
  rw [Category.assoc, relativeFunctorEvaluate_ι, ← Category.assoc, relativeFunctorPost_ι,
    Category.assoc, Category.assoc, vertexFiberMap_ι]
  rw [← Category.assoc (relativeFunctorEvaluate p a v), relativeFunctorEvaluate_ι,
    Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
