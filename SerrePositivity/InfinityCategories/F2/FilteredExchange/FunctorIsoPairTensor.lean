module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoPairPresentation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorPairRightTensor
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerVertexMap

/-!
概要：同じ第二成分との組にした指定同型は、二成分の実射の直積作用と値まで可換する。
方針：両方を元の同型の同じ関手空間の射による像へ戻す。
規約：元の指定同型を保持。使われ方：全右 Hom 比較の輸送因子の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の点同型の組に直積射を作用させると、第一成分の像と同じ第二成分の像の組になる。 -/
lemma functorIsoLiftRight_tensor_heq {P A B C D : SSet.{u}} {f g : P ⟶ A}
    (e : FunctorIso f g) (y : P ⟶ B) (r : A ⟶ C) (s : B ⟶ D) :
    HEq ((functorIsoLiftRight e y).postcomp (r ⊗ₘ s))
      (functorIsoLiftRight (e.postcomp r) (y ≫ s)) := by
  have hs : functorVertex (f ≫ r) =
      ((ihom P).map r).app (Opposite.op ⦋0⦌) (functorVertex f) := by
    apply CategoryTheory.Functor.functorHom_ext
    intro n α
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  have ht : functorVertex (g ≫ r) =
      ((ihom P).map r).app (Opposite.op ⦋0⦌) (functorVertex g) := by
    apply CategoryTheory.Functor.functorHom_ext
    intro n α
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  have hm := vertexIso_map_heq_of_heq (e.postcomp r)
    (VertexIso.map e ((ihom P).map r)) hs ht
    (functorIso_postcomp_vertexMap_heq e r) (functorPairRight (y ≫ s))
  have hr := (functorIsoLiftRight_heq_map (e.postcomp r) (y ≫ s)).trans
    (hm.trans (heq_of_eq (vertexIso_map_comp e ((ihom P).map r) (functorPairRight (y ≫ s)))))
  exact (functorIsoLiftRight_postcomp_heq_map e y (r ⊗ₘ s)).trans
    ((vertexIso_map_heq e (functorPairRight_tensor y r s)).trans hr.symm)

end SerrePositivity.InfinityCategories.F2
