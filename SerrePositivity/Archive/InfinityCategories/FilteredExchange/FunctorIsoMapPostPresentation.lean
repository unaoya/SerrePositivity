module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPairPresentation

/-!
概要：元の後合成同型と、その指定点評価を元の関手空間の作用へ戻す。
方針：同じ後合成の実全単体を評価し、端点表示の移送だけを外す。
規約：元の指定同型を保持。使われ方：始点作用の自然性の指定成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 後合成の全作用を元の係数で評価すると、同じ係数への前合成になる。 -/
lemma functorPostcompositionMap_evaluate {K X Y : SSet.{u}} (q : K ⟶ X) :
    functorPostcompositionMap K X Y ≫ evaluateFunctorAt (functorVertex q) =
      (pre q).app Y := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の後合成の指定同型は、同じ一つの後合成作用による像を保持する。 -/
lemma functorIso_map_post_heq_map {K X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    HEq (e.map_post K) (VertexIso.map e (functorPostcompositionMap K X Y)) := by
  have hcast {α β : Sort (u + 1)} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
    cases h
    rfl
  unfold FunctorIso.map_post
  exact (hcast _ _).trans (hcast _ _)

/-- 元の前合成同型は、同じ関手空間の制限作用による元の像。 -/
lemma functorIso_precomp_vertexMap_heq {K X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (q : K ⟶ X) :
    HEq (e.precomp q) (VertexIso.map e ((pre q).app Y)) := by
  rw [functorIso_precomp_eq_mapIso]
  simp only [VertexIso.map, hoFunctor_map, Functor.toCatHom_toFunctor]
  rfl

end SerrePositivity.InfinityCategories.F2
