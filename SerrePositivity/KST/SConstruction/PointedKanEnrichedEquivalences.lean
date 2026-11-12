module
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedObjects
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.PointedMappingComponents
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EnrichedHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-! # 点つき全基点 π 同型の coherent な可逆性
概要：L9 の点つき Whitehead の逆を、点つき Kan 複体の ∞ 圏の可逆辺へ移す。
方針：基点固定ホモトピーを豊穣 Hom の連結成分・頂点同型へ移す。
規約：元の点つき射そのものの辺の可逆性を証明する。
使われ方：構造射の模型比較を関手 ∞ 圏で反転する際の成分判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全部分圏の豊穣頂点は元の基点固定写像空間の頂点。 -/
lemma pointedKanObject_vertex_eq {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :
    SimplicialCategory.homEquiv' X Y f = familyVertex f.hom := by
  rw [familyVertex_eq_pointedHomVertex]
  rfl

/-- 元の基点固定ホモトピー成分の等式を、豊穣頂点の同型へ移す。 -/
lemma pointedKanObject_nonempty_vertexIso_of_component {X Y : PointedKanObject.{u}}
    (f g : X ⟶ Y) (h : componentOf f.hom = componentOf g.hom) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (SimplicialCategory.homEquiv' X Y f)
      (SimplicialCategory.homEquiv' X Y g)) := by
  rw [pointedKanObject_vertex_eq, pointedKanObject_vertex_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq h

/-- 全基点 π_* 同型の点つき射の coherent な辺は可逆。 -/
lemma pointedKanObject_edge_isInvertible_of_piIsomorphism {X Y : PointedKanObject.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.hom.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) := by
  obtain ⟨g, ⟨HX, hX⟩, ⟨HY, hY⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse f.hom hf
  let g' : Y ⟶ X := ObjectProperty.homMk g
  have h₀ : componentOf (f ≫ g').hom = componentOf (𝟙 X : X ⟶ X).hom :=
    ((piZero_eq_iff_pointedHomotopy (𝟙 X.obj) (f.hom ≫ g)).mpr ⟨HX, hX⟩).symm
  have h₁ : componentOf (g' ≫ f).hom = componentOf (𝟙 Y : Y ⟶ Y).hom :=
    ((piZero_eq_iff_pointedHomotopy (𝟙 Y.obj) (g ≫ f.hom)).mpr ⟨HY, hY⟩).symm
  obtain ⟨e₀⟩ := pointedKanObject_nonempty_vertexIso_of_component (f ≫ g') (𝟙 X) h₀
  obtain ⟨e₁⟩ := pointedKanObject_nonempty_vertexIso_of_component (g' ≫ f) (𝟙 Y) h₁
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse f g' e₀ e₁

end SerrePositivity.KST.SConstruction
