module
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.GroupoidBasedArrow
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-! # Kan 空間の全辺と二面を一つの基点の群で計算する
概要：全区間写像の値を同じ群に取り、元の実三角形の合成関係を回収する。
方針：元の辺のホモトピー圏の射を基点へ移す。平行辺の検出を同時に保持する。
規約：全区間の等号からのみ値を書き換え、群の等号と実円柱の構成を区別する。
使われ方：十二面比較複体の全辺路の消去と、端点固定比較の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {E : SSet.{u}} [KanComplex E]
local instance kanBasedEdgeValueGroupoid : Groupoid (hoFunctor.obj E) :=
  Groupoid.ofIsGroupoid
variable (c : (hoFunctor.obj E))

/-- 元の全区間写像を基点の同じ群へ移した値。 -/
def kanBasedEdgeValue (e : (Δ[1] : SSet.{u}) ⟶ E) : End c :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.groupoidBasedArrow c (SSet.HomotopyCategory.homMk (SSet.Edge.mk' (SSet.yonedaEquiv e)))

/-- 元の端点つき辺の表示では、元の同じ射の基点表示を回収する。 -/
lemma kanBasedEdgeValue_edge {x y : E _⦋0⦌} (a : E.Edge x y) :
    kanBasedEdgeValue c (SSet.yonedaEquiv.symm a.edge) =
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.groupoidBasedArrow c (SSet.HomotopyCategory.homMk a) := by
  obtain ⟨e, hs, ht⟩ := a
  cases hs
  cases ht
  unfold kanBasedEdgeValue
  rw [Equiv.apply_symm_apply]
  rfl

/-- 元の全二単体の三辺は同じ基点の群で合成関係を満たす。 -/
lemma kanBasedEdgeValue_triangle (T : (Δ[2] : SSet.{u}) ⟶ E) :
    kanBasedEdgeValue c (stdSimplex.δ 1 ≫ T) =
      kanBasedEdgeValue c (stdSimplex.δ 0 ≫ T) *
        kanBasedEdgeValue c (stdSimplex.δ 2 ≫ T) := by
  obtain ⟨x, y, z, a, b, d, t, ht⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv T)
  have he : T = SSet.yonedaEquiv.symm t.simplex :=
    (Equiv.symm_apply_apply _ _).symm.trans (congrArg SSet.yonedaEquiv.symm ht).symm
  rw [he, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm,
    kanBasedEdgeValue_edge, kanBasedEdgeValue_edge, kanBasedEdgeValue_edge,
    ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.groupoidBasedArrow_comp, SSet.HomotopyCategory.homMk_comp_homMk t]

/-- 基点から始点へ到達できれば、同じ値を持つ平行辺は元の射の同じ類を表す。 -/
lemma kanBasedEdgeValue_detects {x y : E _⦋0⦌}
    (hx : Nonempty (c ⟶ SSet.HomotopyCategory.mk x)) (a b : E.Edge x y)
    (h : kanBasedEdgeValue c (SSet.yonedaEquiv.symm a.edge) =
      kanBasedEdgeValue c (SSet.yonedaEquiv.symm b.edge)) :
    SSet.HomotopyCategory.homMk a = SSet.HomotopyCategory.homMk b := by
  rw [kanBasedEdgeValue_edge, kanBasedEdgeValue_edge] at h
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.groupoidBasedArrow_injective c hx _ _ h

end SerrePositivity.KST.SConstruction
