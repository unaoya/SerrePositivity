module
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoDoubleEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningPointFiberEvaluation

/-! # 同じ指定同型の二重評価は、二変数の転置でも値を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 内部 Hom を転置して二回評価する写像は、元の二回評価そのもの。 -/
theorem doubleFunctorEvaluation_transpose {K A Y : SSet.{u}}
    (x : K _⦋0⦌) (a : A _⦋0⦌) :
    (internalHomSwapIso K A Y).hom ≫ doubleFunctorEvaluation (Y := Y) a x =
      doubleFunctorEvaluation (Y := Y) x a := by
  have h := congrArg (fun m => m ≫ evaluateFunctorAt (Y := Y) a)
    (internalHomSwapIso_evaluate K A Y x)
  simpa only [Category.assoc, evaluateFunctorAt_post, doubleFunctorEvaluation] using h

/-- 元の同じ同型を転置後に二重評価しても、元の指定された像を保持する。 -/
theorem functorIso_transpose_doubleMap {K A Y : SSet.{u}}
    {F G : K ⟶ (ihom A).obj Y} (e : FunctorIso F G)
    (x : K _⦋0⦌) (a : A _⦋0⦌) :
    HEq (VertexIso.map e.transpose (doubleFunctorEvaluation (Y := Y) a x))
      (VertexIso.map e (doubleFunctorEvaluation (Y := Y) x a)) := by
  unfold FunctorIso.transpose
  have hmap (f g : (ihom K).obj ((ihom A).obj Y) ⟶ Y) (h : f = g) :
      HEq (VertexIso.map e f) (VertexIso.map e g) := by
    cases h
    rfl
  exact (heq_of_eq (F2.vertexIso_map_comp e (internalHomSwapIso K A Y).hom
    (doubleFunctorEvaluation (Y := Y) a x))).trans
      (hmap _ _ (doubleFunctorEvaluation_transpose x a))

end SerrePositivity.KST.Fibration
