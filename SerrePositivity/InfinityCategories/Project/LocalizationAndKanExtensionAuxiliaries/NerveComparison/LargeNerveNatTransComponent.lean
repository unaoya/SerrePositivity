module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LargeNerveNatTransHomotopy

/-!
概要：指定した nerve 円柱の垂直辺。
方針：元の自然変換の成分を同じ円柱で計算する。
規約：HTT 6.2.2.7・5.5.4.15 の集合値層化単位に用いる通常の nerve の計算。
使われ方：同じ自然変換を空間値前層の層化比較へ送る。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 円柱の各垂直辺が、元の自然変換の同じ成分を回収する。 -/
@[cite HTT "6.2.2.7" (partial := special) "集合値層化の単位の通常の nerve での成分。"]
lemma largeNerveNatTransHomotopy_component :
    ∀ {A : Type v} [Category.{u} A] {F G : A ⥤ A} (η : F ⟶ G) (a : A),
      (simplicialHomotopyVertexEdge (largeNerveNatTransHomotopy η) (nerveVertex a)).edge =
        (nerve.edgeMk (η.app a)).edge := by
  intro A hA F G η a
  rw [largeNerveNatTransHomotopy, homotopyOfPrism_vertexEdge]
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change η.app a ≫ G.map (𝟙 a) = η.app a
  rw [G.map_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
