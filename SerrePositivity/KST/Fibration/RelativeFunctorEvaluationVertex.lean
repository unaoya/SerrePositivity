module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-! # 同じ相対関手の頂点評価は、元の全空間の指定点を回収する -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 相対関手の同じ頂点を評価した fiber 点の値。 -/
theorem relativeFunctorEvaluate_vertex_val {A E B : SSet.{u}}
    (p : E ⟶ B) (r : A ⟶ B) (f : A ⟶ E) (hf : f ≫ p = r) (z : A _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p r z).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r f hf)).val = f.app (Opposite.op ⦋0⦌) z := by
  have h := congrArg
    (fun k => k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r f hf))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_ι p r z)
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex z f)

/-- 同じ底上の制限を通して評価しても、元の制限写像の指定点を回収する。 -/
theorem relativeFunctorOverPre_evaluate_val {A Z E B : SSet.{u}}
    (p : E ⟶ B) (r : Z ⟶ B) (t : A ⟶ B) (a : A ⟶ Z) (ha : a ≫ r = t)
    (f : Z ⟶ E) (hf : f ≫ p = r) (z : A _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p (Over.homMk (U := Over.mk t) (V := Over.mk r) a ha) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p t z).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p r f hf)).val =
        (a ≫ f).app (Opposite.op ⦋0⦌) z := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex p
    (Over.homMk (U := Over.mk t) (V := Over.mk r) a ha) f hf
  have he := congrArg
    (fun v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p t) _⦋0⦌ =>
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p t z).app (Opposite.op ⦋0⦌) v).val) ht
  exact he.trans (relativeFunctorEvaluate_vertex_val _ _ _ _ _)

end SerrePositivity.KST.Fibration
