module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：同じ指定同値による前合成から、全写像間の同型を反映する。
方針：指定同値の逆で前合成し、同じ二胞体で逆と順射を相殺する。
規約：各頂点の同型に弱めない。使われ方：G8 の同じ値比較を通じた自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：指定同値で前合成して全族で同型な二つの写像は、元のまま全族で同型。
方針：指定された逆で前合成し、同じ逆順の二胞体を左右で相殺する。
規約：標的は任意の単体集合。使われ方：元の G8 の比較への自然性の復帰。 -/
def functorIsoOfPrecompEquivalence {A B X : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (q : A ⟶ B) (hq : IsQCatEquivalence q) (f g : B ⟶ X)
    (h : FunctorIso (q ≫ f) (q ≫ g)) : FunctorIso f g := by
  let e := hq.choose
  have hf : FunctorIso (e.inv ≫ q ≫ f) f := by
    simpa only [e, IsQCatEquivalence.choose, Category.assoc, Category.id_comp] using FunctorIso.postcomp e.invHomIso f
  have hg : FunctorIso (e.inv ≫ q ≫ g) g := by
    simpa only [e, IsQCatEquivalence.choose, Category.assoc, Category.id_comp] using FunctorIso.postcomp e.invHomIso g
  have hh := FunctorIso.precomp h e.inv
  exact hf.symm ≪≫ hh ≪≫ hg

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
