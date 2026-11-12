module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTrans
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：通常の圏の指定同値を元の nerve 間の同値へ写す。
方針：単位と余単位の自然同型を h Fun の指定同型へ写す。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {D E : Type u} [Category.{u} D] [Category.{u} E]

/-- 概要：通常の圏の指定同値は元の nerve 間の QCat の同値を与える。
方針：単位と余単位の自然同型を h Fun の指定同型へ写す。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def nerveQCatEquivalence (e : D ≌ E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (nerve D) (nerve E) where
  hom := nerveMap e.functor
  inv := nerveMap e.inverse
  homInvIso := by
    change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding D D).obj (e.functor ⋙ e.inverse) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding D D).obj (𝟭 D)
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding D D).mapIso e.unitIso.symm
  invHomIso := by
    change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding E E).obj (e.inverse ⋙ e.functor) ≅
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding E E).obj (𝟭 E)
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding E E).mapIso e.counitIso

/-- 概要：通常の同値関手の nerve は元の quasicategory の同値。
方針：単位と余単位の自然同型を h Fun の指定同型へ写す。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma nerveMap_isQCatEquivalence (F :
    D ⥤ E) [F.IsEquivalence] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (nerveMap F) :=
  (nerveQCatEquivalence F.asEquivalence).isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
