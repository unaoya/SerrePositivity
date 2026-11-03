module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDown
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseDownFunctorCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UliftFunctorSpaceInvNaturality

/-!
概要：関手空間のホモトピー圏の宇宙下降は、元の射の前後合成と厳密に可換する。
方針：内部 Hom の宇宙同型の逆の自然性と、全ホモトピー圏の下降の自然性を合成する。
規約：指定射・指定同型の像を保持。使われ方：native な四射の値比較の小宇宙移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 関手空間の下降は元の射による後合成と厳密に可換する。 -/
lemma functorSpaceDown_post {A X Y : SSet.{u}} (q : X ⟶ Y) :
    functorSpaceDown.{u, v} A X ⋙ SSet.mapHomotopyCategory ((ihom A).map q) =
    SSet.mapHomotopyCategory
      ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).map ((SSet.uliftFunctor.{v, u}).map q)) ⋙
        functorSpaceDown.{u, v} A Y := by
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k)
    (uliftFunctorSpaceInv_post.{u, v} (A := A) q)
  simp only [mapHomotopyCategory_comp_eq] at hh
  unfold functorSpaceDown
  rw [Functor.assoc, universeHomotopyDown_naturality, ← Functor.assoc, hh, Functor.assoc]

/-- 関手空間の下降は元の射による前合成と厳密に可換する。 -/
lemma functorSpaceDown_pre {A X Y : SSet.{u}} (q : A ⟶ X) :
    functorSpaceDown.{u, v} X Y ⋙ SSet.mapHomotopyCategory ((pre q).app Y) =
    SSet.mapHomotopyCategory
      ((pre ((SSet.uliftFunctor.{v, u}).map q)).app ((SSet.uliftFunctor.{v, u}).obj Y)) ⋙
        functorSpaceDown.{u, v} A Y := by
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k)
    (uliftFunctorSpaceInv_pre.{u, v} (Y := Y) q)
  simp only [mapHomotopyCategory_comp_eq] at hh
  unfold functorSpaceDown
  rw [Functor.assoc, universeHomotopyDown_naturality, ← Functor.assoc, hh, Functor.assoc]

end SerrePositivity.InfinityCategories.F2
