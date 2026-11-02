module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.F1B.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Core.CatInfinity.VertexIsoTerminalEquality

/-!
概要：元の関手同型の前合成の成分を、同じ元の同型の元の点での評価へ戻す。
方針：一点評価の自然性と同じ指定値の像を使う。
規約：指定値を保持。使われ方：底上の制限に対する後合成比較の成分の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定関手同型の前合成の成分は、同じ元の点の像での元の指定成分。 -/
lemma functorIso_app_precomp_heq {W X Y : SSet.{u}}
    [Quasicategory W] [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) (q : W ⟶ X) (x : W _⦋0⦌) :
    HEq ((e.precomp q).app x) (e.app (q.app _ x)) := by
  have h := functorIso_app_heq_evaluate (e.precomp q) x
  rw [functorIso_precomp_eq_mapIso] at h
  exact h.trans ((heq_of_eq (vertexIso_map_comp e ((pre q).app Y) (evaluateFunctorAt x))).trans
    ((vertexIso_map_heq e (evaluateFunctorAt_pre q x)).trans
      (functorIso_app_heq_evaluate e (q.app _ x)).symm))

/-- 元の入力頂点の厳密な表示変更は、同じ指定関手同型の成分の値を保持する。 -/
lemma functorIso_app_heq_of_vertex_eq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) {x x' : X _⦋0⦌} (h : x = x') :
    HEq (e.app x) (e.app x') := by
  subst x'
  rfl

end SerrePositivity.InfinityCategories.F2
