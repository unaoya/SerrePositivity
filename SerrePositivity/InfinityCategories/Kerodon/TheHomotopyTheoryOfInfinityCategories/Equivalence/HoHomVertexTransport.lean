module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

/-!
概要：指定した頂点の等式を保持するホモトピー圏の射の移送。
方針：元のホモトピー圏の関手作用を、端点の等式の同型で輸送する。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049）の関手性と、元の錐の全射の評価。
規約：大きい構成の本文を展開せず、一般の射を固定して使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 元の関手作用を、指定した端点の等式に沿って移す。 -/
def hoHomMapWithVertexEqualities {A B : SSet.{u}} (f : A ⟶ B)
    {x y : A _⦋0⦌} {x' y' : B _⦋0⦌}
    (hx : f.app (Opposite.op ⦋0⦌) x = x') (hy : f.app (Opposite.op ⦋0⦌) y = y')
    (β : (SSet.HomotopyCategory.mk x : hoFunctor.obj A) ⟶ SSet.HomotopyCategory.mk y) :
    (SSet.HomotopyCategory.mk x' : hoFunctor.obj B) ⟶ SSet.HomotopyCategory.mk y' :=
  eqToHom (congrArg SSet.HomotopyCategory.mk hx).symm ≫
    (hoFunctor.map f).toFunctor.map β ≫ eqToHom (congrArg SSet.HomotopyCategory.mk hy)

/-- 端点の移送は、元の単体的関手の合成と整合する。 -/
lemma hoHomMapWithVertexEqualities_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    {x y : A _⦋0⦌} {x' y' : B _⦋0⦌} {x'' y'' : C _⦋0⦌}
    (hx : f.app (Opposite.op ⦋0⦌) x = x') (hy : f.app (Opposite.op ⦋0⦌) y = y')
    (hx' : g.app (Opposite.op ⦋0⦌) x' = x'') (hy' : g.app (Opposite.op ⦋0⦌) y' = y'')
    (β : (SSet.HomotopyCategory.mk x : hoFunctor.obj A) ⟶ SSet.HomotopyCategory.mk y) :
    hoHomMapWithVertexEqualities g hx' hy' (hoHomMapWithVertexEqualities f hx hy β) =
      hoHomMapWithVertexEqualities (f ≫ g)
        ((congrArg (g.app (Opposite.op ⦋0⦌)) hx).trans hx')
        ((congrArg (g.app (Opposite.op ⦋0⦌)) hy).trans hy') β := by
  cases hx
  cases hy
  cases hx'
  cases hy'
  simp only [hoHomMapWithVertexEqualities, eqToHom_refl, Category.id_comp, Category.comp_id]
  have he : (hoFunctor.map (f ≫ g)).toFunctor =
      (hoFunctor.map f).toFunctor ⋙ (hoFunctor.map g).toFunctor := by
    simpa only [Cat.Hom.comp_toFunctor] using
      congrArg Cat.Hom.toFunctor (hoFunctor.map_comp f g)
  have hh := CategoryTheory.Functor.congr_hom he β
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using hh.symm


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
