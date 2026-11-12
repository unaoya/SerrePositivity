module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPair
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：同じ第二成分との組にした指定同型を、元の同型の同じ一つの像へ戻す。
方針：実端点の表示変更だけを外し、後合成を同じ頂点同型の像へ合成する。
規約：指定値を選び直さない。使われ方：評価・輸送の全係数作用の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定点同型と第二成分の組は、同じ関手空間の射による指定像を保つ。 -/
lemma functorIsoLiftRight_heq_map {P A B : SSet.{u}} {f g : P ⟶ A}
    (e : FunctorIso f g) (y : P ⟶ B) :
    HEq (functorIsoLiftRight e y) (VertexIso.map e (functorPairRight y)) := by
  have hcast {α β : Sort (u + 1)} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
    cases h
    rfl
  unfold functorIsoLiftRight
  exact (hcast _ _).trans (hcast _ _)

/-- 組にした指定同型の後合成も、元の指定値の同じ単一の像となる。 -/
lemma functorIsoLiftRight_postcomp_heq_map {P A B C : SSet.{u}} {f g : P ⟶ A}
    (e : FunctorIso f g) (y : P ⟶ B) (q : A ⊗ B ⟶ C) :
    HEq ((functorIsoLiftRight e y).postcomp q)
      (VertexIso.map e (functorPairRight y ≫ (ihom P).map q)) := by
  have he := functorIsoLiftRight_heq_map e y
  have hs := (functorPairRight_vertex f y).symm
  have ht := (functorPairRight_vertex g y).symm
  rw [functorIso_postcomp_eq_mapIso]
  exact (vertexIso_map_heq_of_heq _ _ hs ht he ((ihom P).map q)).trans
    (heq_of_eq (vertexIso_map_comp _ _ _))

end SerrePositivity.InfinityCategories.F2
