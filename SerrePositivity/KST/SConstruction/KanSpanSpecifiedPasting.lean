module
public import SerrePositivity.KST.SConstruction.KanSpanPastingChoices
public import SerrePositivity.KST.SConstruction.AnodyneExtensionSpecifiedVertices
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.KanMappingSpanComposition

/-! # 元の指定辺・指定三角形を保つ span 貼り合わせの頂点
概要：元の三辺を持つ実三角形を可縮選択空間へ入れ、その辺と二単体を厳密に回収する。
方針：指定三角形のホーン制限を照合し、既存の逆・合成証人から同じ合成辺の外側三角形を得る。
規約：既存の選んだ適合辺を置き換えず、三角形の追加だけで全選択空間へ含める。
使われ方：元の K 適合辺を保ったまま全パラメータの貼り合わせ選択を延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 指定した元の実三角形のホーン制限は、元の二脚の共通パラメータへの貼り合わせ。 -/
lemma kanSpanTriangle_restrict {K : SSet.{u}} {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} {e : K.Edge x y} (T : SSet.Edge.CompStruct a e b) :
    (horn 2 (0 : Fin 3)).ι ≫ SSet.yonedaEquiv.symm T.simplex = kanSpanHorn a b := by
  apply horn₂₀.isPushout.hom_ext
  · simp only [← Category.assoc, horn.ι_ι, kanSpanHorn_source,
      stdSimplex.δ_comp_yonedaEquiv_symm, T.d₂]
  · simp only [← Category.assoc, horn.ι_ι, kanSpanHorn_target,
      stdSimplex.δ_comp_yonedaEquiv_symm, T.d₁]

/-- 元の三辺を保つ指定三角形を、全貼り合わせ空間の実頂点へ入れる。 -/
def kanSpanPastingVertex {K : SSet.{u}} {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} {e : K.Edge x y} (T : SSet.Edge.CompStruct a e b) :
    (kanSpanPastingChoices a b) _⦋0⦌ :=
  anodyneExtensionVertex _ _ (SSet.yonedaEquiv.symm T.simplex) (kanSpanTriangle_restrict T)

/-- 指定頂点を評価すると元の実三角形そのものを厳密に回収する。 -/
lemma kanSpanPastingAt_vertex {K : SSet.{u}} {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} {e : K.Edge x y} (T : SSet.Edge.CompStruct a e b) :
    kanSpanPastingAt a b (kanSpanPastingVertex T) = SSet.yonedaEquiv.symm T.simplex :=
  anodyneExtensionAt_vertex _ _ _ _

/-- 元の合成辺は、指定頂点の評価で同じ raw な辺として厳密に回収する。 -/
lemma kanSpanPastedEdge_vertex {K : SSet.{u}} {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} {e : K.Edge x y} (T : SSet.Edge.CompStruct a e b) :
    kanSpanPastedEdge a b (kanSpanPastingVertex T) = e := by
  apply SSet.Edge.ext
  change K.δ 0 (SSet.yonedaEquiv (kanSpanPastingAt a b (kanSpanPastingVertex T))) = e.edge
  rw [kanSpanPastingAt_vertex, Equiv.apply_symm_apply, T.d₀]

/-- 指定頂点での三角形は、元の二単体をそのまま回収する。 -/
lemma kanSpanPastedTriangle_vertex_simplex {K : SSet.{u}} {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} {e : K.Edge x y} (T : SSet.Edge.CompStruct a e b) :
    (kanSpanPastedTriangle a b (kanSpanPastingVertex T)).simplex = T.simplex := by
  change SSet.yonedaEquiv (kanSpanPastingAt a b (kanSpanPastingVertex T)) = _
  rw [kanSpanPastingAt_vertex, Equiv.apply_symm_apply]

/-- 既存の逆・合成証人の同じ合成辺を保つ、元の二脚の外側三角形。 -/
def kanMappingSpanOuterTriangle {K : SSet.{u}} [KanComplex K] {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} (t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition a b) :
    SSet.Edge.CompStruct a t.edge b := by
  have hc : SSet.HomotopyCategory.homMk a ≫ SSet.HomotopyCategory.homMk t.edge =
      SSet.HomotopyCategory.homMk b := by
    rw [← SSet.HomotopyCategory.homMk_comp_homMk t.triangle, ← Category.assoc,
      SSet.HomotopyCategory.homMk_comp_homMk t.inverseLeft,
      SSet.HomotopyCategory.homMk_id, Category.id_comp]
  exact SSet.Edge.CompStruct.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hc).some

/-- 元の選んだ合成辺を保ったまま、可縮な全貼り合わせ空間へ入れる。 -/
def kanMappingSpanPastingVertex {K : SSet.{u}} [KanComplex K] {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} (t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition a b) :
    (kanSpanPastingChoices a b) _⦋0⦌ :=
  kanSpanPastingVertex (kanMappingSpanOuterTriangle t)

/-- 以前の逆・合成による指定辺は、全貼り合わせ空間の評価で厳密に保たれる。 -/
lemma kanSpanPastedEdge_mappingSpanVertex {K : SSet.{u}} [KanComplex K] {z x y : K _⦋0⦌}
    {a : K.Edge z x} {b : K.Edge z y} (t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition a b) :
    kanSpanPastedEdge a b (kanMappingSpanPastingVertex t) = t.edge :=
  kanSpanPastedEdge_vertex (kanMappingSpanOuterTriangle t)

end SerrePositivity.KST.SConstruction
