module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoCurryPresentation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoComponentTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の指定同型の curry の一点成分を、元の同じ係数への制限に同定する。
方針：全関手空間の curry と評価の厳密な交換を用いる。
規約：指定比較を保持。使われ方：全三角形の輸送比較の一点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全関手空間の curry の一点評価は、同じ係数を固定する前合成。 -/
lemma functorSpaceCurryMap_evaluate {A B X : SSet.{u}} (l : B _⦋0⦌) :
    functorSpaceCurryMap A B X ≫ evaluateFunctorAt l =
      (pre (lift (𝟙 A) (SSet.const l))).app X := by
  apply uncurry_injective
  rw [functorSpaceCurryMap, curry_evaluateFunctorAt_vertex,
    uncurry_natural_left, uncurry_curry]
  have hp : (A ◁ lift (SSet.const l) (𝟙 ((ihom (A ⊗ B)).obj X))) ≫
      (α_ A B ((ihom (A ⊗ B)).obj X)).inv =
      lift (𝟙 A) (SSet.const l) ▷ ((ihom (A ⊗ B)).obj X) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, hp]
  exact (MonoidalClosed.uncurry_pre (lift (𝟙 A) (SSet.const l)) X).symm

/-- 元の指定同型の curry の一点成分は、同じ係数で制限した元の指定同型。 -/
lemma functorIso_curry_app_heq_precomp {A B X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] {f g : A ⊗ B ⟶ X}
    (e : FunctorIso f g) (l : B _⦋0⦌) :
    HEq (e.curry.app l) (e.precomp (lift (𝟙 A) (SSet.const l))) := by
  have h := vertexIso_map_heq_of_heq e.curry
    (VertexIso.map e (functorSpaceCurryMap A B X))
    (functorSpaceCurryMap_vertex f).symm (functorSpaceCurryMap_vertex g).symm
    (functorIso_curry_heq_map e) (evaluateFunctorAt l)
  refine (functorIso_app_heq_evaluate e.curry l).trans (h.trans ?_)
  rw [vertexIso_map_comp, functorIso_precomp_eq_mapIso]
  exact vertexIso_map_heq e (functorSpaceCurryMap_evaluate l)

end SerrePositivity.InfinityCategories.F2
