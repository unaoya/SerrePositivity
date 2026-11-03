module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorCurryHom
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.CatInfinity.VertexIsoTerminalEquality

/-!
概要：相対 curry の豊穣作用の一点評価は、元の族の同じ一点への制限である。
方針：通常の curry の評価式と相対 uncurry の自然性を合成する。
規約：指定頂点と指定同型を保持。使われ方：元の三角形比較を一点で評価する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (L : SSet.{u}) (l : L _⦋0⦌)

/-- 相対 curry を指定係数で評価すると元の全族の同じ係数での制限になる。 -/
lemma relativeFunctorCurryHom_evaluate :
    relativeFunctorCurryHom p a L ≫ evaluateFunctorAt l =
      relativeFunctorPre p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l)) := by
  rw [relativeFunctorCurryHom, curry_evaluateFunctorAt_vertex]
  apply relativeFunctorUncurry_injective p a
  rw [relativeFunctorUncurry_naturality, relativeFunctorUncurry_curry]
  change _ = relativeFunctorUncurry ((𝟙 _) ≫ relativeFunctorOverPre p
    (Over.homMk (U := Over.mk a) (V := Over.mk (fst A L ≫ a))
      (lift (𝟙 A) (SSet.const l)) rfl))
  rw [relativeFunctorOverPre_uncurry, ← Category.assoc]
  congr 1

/-- 指定比較同型の相対 curry を評価しても、元の比較の同じ制限が得られる。 -/
lemma relativeFunctorCurryHom_vertexIso_evaluate
    {x y : (relativeFunctorSpace p (fst A L ≫ a)) _⦋0⦌} (e : VertexIso x y) :
    HEq (VertexIso.map (VertexIso.map e (relativeFunctorCurryHom p a L)) (evaluateFunctorAt l))
      (VertexIso.map e
        (relativeFunctorPre p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l)))) := by
  exact (heq_of_eq (vertexIso_map_comp e (relativeFunctorCurryHom p a L)
    (evaluateFunctorAt l))).trans (vertexIso_map_heq e (relativeFunctorCurryHom_evaluate p a L l))

end SerrePositivity.InfinityCategories.F2
