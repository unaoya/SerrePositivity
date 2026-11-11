module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EnrichedHomotopy

/-!
概要：strict transport の像の対象ごとの同値が定める coherent な辺の可逆性。
方針：自然変換を単体的圏の通常の射にし、strict な逆条件を coherent nerve へ移す。
規約：同値性は変換の各成分について要求する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の比較を coherent な同値へ接続する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：strict な自然変換を像の単体的圏の通常の射にする。
方針：変換空間の頂点をテンソル単位からの射へ移す。
規約：通常の射の underlying category は既存の豊穣圏から得たもの。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent nerve の辺としての自然変換。 -/
def strictTransportImageHom {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) : F ⟶ G :=
  (SSet.unitHomEquiv _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex η)

/-- 概要：自然変換から作った像の射の豊穣表示は元の変換の頂点。
方針：テンソル単位からの射と頂点の全単射の往復を使う。
規約：始域と終域は strict transport の像の対象。
使われ方：Kerodon §2.4.3（Tag 00KM）、strict な逆条件と豊穣 Hom の逆条件の同定。 -/
lemma strictTransportImageHom_vertex {C : Type u} [Category.{u} C]
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :
    SimplicialCategory.homEquiv' F G (strictTransportImageHom η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex η :=
  (SSet.unitHomEquiv _).apply_symm_apply _

/-- 概要：自然変換の合成は像の通常の射の合成と整合する。
方針：各次数と各対象の内部 Hom の入力で合成を計算する。
規約：η の後に θ を合成する。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な逆射の二つの合成条件。 -/
lemma strictTransportImageHom_comp {C : Type u} [Category.{u} C]
    {F G H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (θ : G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ H.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :
    strictTransportImageHom (η ≫ θ) = strictTransportImageHom η ≫ strictTransportImageHom θ := by
  apply (SimplicialCategory.homEquiv' F H).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp, strictTransportImageHom_vertex,
    strictTransportImageHom_vertex, strictTransportImageHom_vertex]
  rfl

/-- 概要：自然変換の恒等射は像の恒等射になる。
方針：豊穣表示の単射性を使い、恒等変換の成分を計算する。
規約：図式の対象を固定する。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な逆条件の恒等射の表示。 -/
lemma strictTransportImageHom_id {C : Type u} [Category.{u} C]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C) :
    strictTransportImageHom (𝟙 (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) = 𝟙 F := by
  apply (SimplicialCategory.homEquiv' F F).injective
  rw [strictTransportImageHom_vertex]
  rfl

/-- 概要：像の図式間の対象ごとの同値は coherent nerve の可逆な辺を定める。
方針：strict な逆変換を取り、豊穣 Hom 内の二つの比較を coherent な逆条件に移す。
規約：結論は指定された変換から作った辺そのものの可逆性。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、実現写像の同値判定に用いる strict な比較の接続。 -/
lemma strictTransportImageHom_isInvertible_of_pointwise
    {C : Type u} [Category.{u} C] {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (strictTransportImageHom η)) := by
  obtain ⟨θ, ⟨hu⟩, ⟨hc⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_strictTransportImageInverse F G η hη
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse
    (strictTransportImageHom η) (strictTransportImageHom θ)
  · rw [← strictTransportImageHom_comp, ← strictTransportImageHom_id F,
      strictTransportImageHom_vertex, strictTransportImageHom_vertex]
    exact hu
  · rw [← strictTransportImageHom_comp, ← strictTransportImageHom_id G,
      strictTransportImageHom_vertex, strictTransportImageHom_vertex]
    exact hc

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
