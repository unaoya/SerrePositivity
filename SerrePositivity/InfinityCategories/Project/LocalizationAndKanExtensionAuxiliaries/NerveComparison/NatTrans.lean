module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FunctorVertex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：通常の自然変換を元の nerve 間の関手圏の h の射へ写す。
方針：関手圏の nerve の辺の類を指数比較で写し、証明済みの頂点公式で両端を揃える。
規約：元の指定された自然変換の辺をそのまま使う。
使われ方：古典随伴の単位・余単位を QCat の二胞体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：指数比較で写した関手頂点は元の nerve の頂点と同じ対象を表す。
方針：頂点公式を h の対象の等式へ写して同型にする。
規約：対象の輸送だけを行い、自然変換を選ばない。
使われ方：指定された自然変換の両端の整合。 -/
def nerveFunctorVertexIso {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) :
    (HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ F)) : hoFunctor.obj ((ihom (nerve C)).obj (nerve D))) ≅
        HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F)) :=
  eqToIso (congrArg (fun x : ((ihom (nerve C)).obj (nerve D)).obj (Opposite.op ⦋0⦌) ↦
    HomotopyCategory.mk x) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorCategoryIso_vertex F))

/-- 概要：通常の自然変換はその nerve 間の指定された関手の間の h の射を与える。
方針：nerve の辺の類を関手圏の比較同型で写す。
規約：対象は元の nerveMap F と nerveMap G。
使われ方：古典随伴の単位と余単位の表現。 -/
def nerveNatTransHom {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (η : F ⟶ G) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap F) (nerveMap G) :=
  (nerveFunctorVertexIso F).inv ≫
    HomotopyCategory.homMk ((nerve.edgeMk η).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom) ≫
      (nerveFunctorVertexIso G).hom

/-- 概要：通常の恒等自然変換は元の関手圏の h の恒等射へ写る。
方針：nerve の恒等辺の類と端点の輸送の逆性を消す。
規約：指定された元の関手の恒等射。
使われ方：自然変換の古典比較の関手性。 -/
lemma nerveNatTransHom_id {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    nerveNatTransHom (𝟙 F) = 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F))) := by
  simp only [nerveNatTransHom, nerve.edgeMk_id, SSet.Edge.map_id]
  erw [HomotopyCategory.homMk_id]
  rw [Category.id_comp]
  exact (nerveFunctorVertexIso F).inv_hom_id

/-- 概要：通常の自然変換の合成は元の関手圏の h の合成へ写る。
方針：nerve の合成三角形の類の式に比較関手を適用し、中央の端点輸送を消去する。
規約：二つの指定された自然変換をその順序で合成する。
使われ方：古典随伴の三角恒等式を h の射へ移す。 -/
lemma nerveNatTransHom_comp {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    nerveNatTransHom (η ≫ θ) = nerveNatTransHom η ≫ nerveNatTransHom θ := by
  obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff η θ (η ≫ θ)).2 rfl
  have ht := HomotopyCategory.homMk_comp_homMk (t.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom)
  simp only [nerveNatTransHom, Category.assoc, Iso.hom_inv_id_assoc]
  have he := congrArg (fun m ↦
    (nerveFunctorVertexIso F).inv ≫ m ≫ (nerveFunctorVertexIso H).hom) ht.symm
  simpa only [Category.assoc] using he

/-- 概要：通常の関手と自然変換を元の nerve 間の関手圏の h に写す関手。
方針：頂点公式で指定した対象と自然変換の辺の類を使う。
規約：恒等射と合成の保存は前の二つの補題で証明済み。
使われ方：古典随伴の三角恒等式と Kan の自然性の移送。 -/
def nerveFunctorHomEmbedding (C D : Type u) [Category.{u} C] [Category.{u} D] :
    (C ⥤ D) ⥤ hoFunctor.obj ((ihom (nerve C)).obj (nerve D)) where
  obj F := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F))
  map η := nerveNatTransHom η
  map_id F := nerveNatTransHom_id F
  map_comp η θ := nerveNatTransHom_comp η θ


end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
