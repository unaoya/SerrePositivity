module
public import SerrePositivity.KST.Fibration.DoubleEvaluationTranspose

/-! # 同じ curry 同型の二重評価は、元の直積頂点での同じ評価 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- curry の二重評価写像は、元の同じ直積頂点での評価。 -/
theorem doubleFunctorEvaluation_curry {A K Y : SSet.{u}}
    (a : A _⦋0⦌) (x : K _⦋0⦌) :
    functorSpaceCurryMap A K Y ≫ doubleFunctorEvaluation (Y := Y) x a =
      evaluateFunctorAt (a, x) := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation, ← Category.assoc, F2.functorSpaceCurryMap_evaluate,
    evaluateFunctorAt_pre]
  apply congrArg (fun z => evaluateFunctorAt (Y := Y) z)
  change (a, PinchedHom.constant x 0) = (a, x)
  rw [pinchedConstant_zero]

/-- 指定同型を curry 後に二重評価しても、元の同じ直積成分を保持する。 -/
theorem functorIso_curry_doubleMap {A K Y : SSet.{u}} [Quasicategory Y]
    {F G : A ⊗ K ⟶ Y} (e : FunctorIso F G) (a : A _⦋0⦌) (x : K _⦋0⦌) :
    HEq (VertexIso.map e.curry (doubleFunctorEvaluation (Y := Y) x a))
      (VertexIso.map e (evaluateFunctorAt (a, x))) := by
  have hm := F2.vertexIso_map_heq_of_heq e.curry
    (VertexIso.map e (functorSpaceCurryMap A K Y))
    (functorSpaceCurryMap_vertex F).symm (functorSpaceCurryMap_vertex G).symm
    (F2.functorIso_curry_heq_map e) (doubleFunctorEvaluation (Y := Y) x a)
  exact hm.trans ((heq_of_eq (F2.vertexIso_map_comp e (functorSpaceCurryMap A K Y)
    (doubleFunctorEvaluation (Y := Y) x a))).trans
      (F2.vertexIso_map_heq e (doubleFunctorEvaluation_curry a x)))

end SerrePositivity.KST.Fibration
