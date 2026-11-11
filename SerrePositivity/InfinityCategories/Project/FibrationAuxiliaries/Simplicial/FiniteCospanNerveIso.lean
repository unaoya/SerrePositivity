module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanNerveIso
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.OrderDualNerveIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite

/-!
概要：標準 cospan ホーンを三点の有限半順序 nerve と厳密に同定する。
方針：span の同型を反転し、順序双対とホーンの反転同型を合成する。
規約：元の反転写像と全ての面・退化を保持する。
使われ方：Ind の有限半順序極限を元の標準 cospan に移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- cospan の有限三点添字。 -/
abbrev FiniteCospanIndex := OrderDual _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}

/-- 元の標準 cospan と有限半順序 nerve の同型。 -/
def finiteCospanNerveIso : nerve FiniteCospanIndex.{u} ≅ (horn 2 2 : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderDualNerveIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex ≪≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex ≪≫
    SSet.opFunctor.mapIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 0).symm

/-- 全単体上で、元の span の反転と同じ比較写像を回収する。 -/
lemma finiteCospanNerveIso_hom_reverse :
    finiteCospanNerveIso.{u}.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 0).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderDualNerveIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex).hom ≫
        SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.hom := by
  simp only [finiteCospanNerveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    CategoryTheory.Functor.mapIso_hom, Iso.inv_hom_id, Category.comp_id]

/-- 全ての面・退化による制限を、元の単体と同じ作用素で保持する。 -/
lemma finiteCospanNerveIso_hom_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (nerve FiniteCospanIndex.{u}).map α ≫ finiteCospanNerveIso.{u}.hom.app m =
      finiteCospanNerveIso.{u}.hom.app n ≫ (horn 2 2 : SSet.{u}).map α :=
  finiteCospanNerveIso.{u}.hom.naturality α

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
