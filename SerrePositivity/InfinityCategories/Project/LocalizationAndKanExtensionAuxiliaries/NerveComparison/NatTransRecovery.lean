module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.HomotopyRecovery
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTrans

/-!
概要：指定された nerve 関手間の h Fun の射から通常の自然変換を復元する。
方針：辺の挿入と指数比較の充満忠実性を指定関手頂点へ移す。
規約：対象だけでなく射の全単射を与える。
使われ方：B5 の古典随伴の逆方向の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：指定関手頂点での埋め込みは辺の挿入と指数比較の合成に同型。
方針：証明済みの関手頂点の同型で両端を揃える。
規約：自然性は指定された自然変換の辺の類の公式。
使われ方：充満忠実性の移送。 -/
def nerveFunctorHomEmbeddingIso (C D : Type u) [Category.{u} C] [Category.{u} D] :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyInclusion (C ⥤ D) ⋙ mapHomotopyCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom ≅
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding C D :=
  NatIso.ofComponents (fun F ↦ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorVertexIso F) (fun η ↦ by
    simp only [Functor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyInclusion, mapHomotopyCategory_map_homMk,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom,
      Iso.hom_inv_id_assoc])

/-- 概要：通常の自然変換から元の nerve 関手間の h Fun の射への対応は充満忠実。
方針：nerve の辺の挿入と指数比較の同値から移送する。
規約：任意の指定された二つの関手について全単射を与える。
使われ方：単位・余単位の復元と三角恒等式の反映。 -/
def nerveFunctorHomEmbedding_fullyFaithful (C D : Type u) [Category.{u} C] [Category.{u} D] :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding C D).FullyFaithful := by
  let e := Cat.equivOfIso (hoFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D))
  have h : (mapHomotopyCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom).FullyFaithful :=
    e.fullyFaithfulFunctor
  exact ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveHomotopyInclusion_fullyFaithful (C ⥤ D)).comp h).ofIso
    (nerveFunctorHomEmbeddingIso C D)

/-- 概要：通常の自然変換と元の nerve 間の関手圏の h の射の全単射。
方針：指定頂点への埋め込みの充満忠実性を使う。
規約：順方向は既存の kanNerveNatTransHom。
使われ方：元の単位・余単位の逆方向の回収。 -/
def nerveNatTransHomEquiv {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F G : C ⥤ D) : (F ⟶ G) ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap F) (nerveMap G) :=
  (nerveFunctorHomEmbedding_fullyFaithful C D).homEquiv

/-- 概要：全単射の順方向は指定した自然変換の辺の類に等しい。
方針：充満忠実性の全単射の順方向の定義を読む。
規約：端点の同型による輸送を含む既存の表示を保つ。
使われ方：左右 whiskering の公式による随伴の反映。 -/
lemma nerveNatTransHomEquiv_apply {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) :
    nerveNatTransHomEquiv F G η = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom η := rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
