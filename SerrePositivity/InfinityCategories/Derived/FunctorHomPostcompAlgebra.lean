module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomGeneral
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompAlgebra
/-!
概要：任意の全関手射の二段後合成と前後合成の一致を証明する。
方針：同じ関手空間の射の等式を h の実関手へ写す。
規約：可逆性は不要。使われ方：K-flat 射の包含後の経路照合。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
lemma functorHom_precomp_postcomp {A X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorHom f g) (p : A ⟶ X) (q : Y ⟶ Z) :
    (SSet.mapHomotopyCategory ((ihom A).map q)).map
      ((SSet.mapHomotopyCategory ((pre p).app Y)).map e) =
    (SSet.mapHomotopyCategory ((pre p).app Z)).map
      ((SSet.mapHomotopyCategory ((ihom X).map q)).map e) := by
  have hn := (pre p).naturality q
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k) hn
  rw [F2.mapHomotopyCategory_comp_eq, F2.mapHomotopyCategory_comp_eq] at hh
  exact (eq_of_heq (functorMapHom_heq_of_functor_eq hh e)).symm
end
end SerrePositivity.InfinityCategories
