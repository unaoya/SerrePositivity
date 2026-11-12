module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDown
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseHomotopyFaithful

/-!
概要：関手空間の宇宙下降が、元の指定関手同型の等式を反映する。
方針：内部 Hom の宇宙同型と、ホモトピー圏の下降の忠実性を合成する。
規約：両端の射を固定する。使われ方：小宇宙の模型 path の等式の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 関手空間の宇宙下降は、射の類の等式を反映する。 -/
lemma functorSpaceDown_faithful (X Y : SSet.{u}) :
    (functorSpaceDown.{u, v} X Y).Faithful := by
  let e := uliftFunctorSpaceIso.{u, v} X Y
  have : (SSet.mapHomotopyCategory e.inv).Faithful :=
    (Cat.equivOfIso (hoFunctor.mapIso e.symm)).fullyFaithfulFunctor.faithful
  have := universeHomotopyDown_faithful.{u, v} ((ihom X).obj Y)
  unfold functorSpaceDown
  infer_instance

/-- 同じ持ち上げた二射間の指定同型は、下降した指定値の等式から比較できる。 -/
lemma functorIsoDown_injective {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y} :
    Function.Injective
      (fun e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f)
        ((SSet.uliftFunctor.{v, u}).map g) => functorIsoDown e) := by
  have := functorSpaceDown_faithful.{u, v} X Y
  intro e d h
  apply (functorSpaceDown.{u, v} X Y).mapIso_injective
  exact (functorIsoDown_eq_mapIso e).symm.trans (h.trans (functorIsoDown_eq_mapIso d))

end SerrePositivity.InfinityCategories.F2
