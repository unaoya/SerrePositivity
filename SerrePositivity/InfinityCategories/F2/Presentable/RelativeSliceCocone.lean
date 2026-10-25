module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceUnderIso
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Core.InitialHomotopy
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeRestriction

/-!
概要：元の対象上の図式の全増大余錐を、元の全余錐への coslice 辺から構成する。
方針：二つの点の join と区間の同型、および join の再結合を使う。
規約：元の全増大図式を固定する。
使われ方：μ-small compact 図式の元の対象上での filtered 因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：固定対象上の図式を元の圏の全余錐として読む。
方針：元の slice 図式を全 uncurry する。
規約：元の全図式を保つ。
使われ方：compact 図式の元の表示段への全因子化。 -/
def sliceDiagramCocone {K C : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ C}
    (a : K ⟶ sliceOver x) : JoinCocone (a ≫ sliceOverProjection x) :=
  ⟨sliceOverUncurry a, sliceOverUncurry_projection a⟩

/-- 概要：全 slice 図式の元の余錐頂点は元の固定点射。
方針：全 uncurry の右固定条件を使う。
規約：点射そのものの厳密な等式。
使われ方：余錐から slice 内への curry。 -/
lemma sliceDiagramCocone_point {K C : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ C}
    (a : K ⟶ sliceOver x) : SSet.yonedaEquiv.symm (sliceDiagramCocone a).vertex = x := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (joinInr K Δ[0] ≫ sliceOverUncurry a)) = x
  rw [Equiv.symm_apply_apply, sliceOverUncurry_fixed]

/-- 概要：元の全余錐へ至る辺の全三因子表示。
方針：coslice 辺を区間として全展開し、二点の join 表示へ戻す。
規約：元の辺の高次成分を保持する。
使われ方：元の対象上の全余錐の構成。 -/
def relativeSliceCoconeMap {K C : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ C}
    (a : K ⟶ sliceOver x) {d : (sliceUnder (a ≫ sliceOverProjection x)) _⦋0⦌}
    (e : (sliceUnder (a ≫ sliceOverProjection x)).Edge d (sliceDiagramCocone a)) :
    join (join K Δ[0]) Δ[0] ⟶ C :=
  (joinAssociator K Δ[0] Δ[0]).hom ≫ joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom ≫
    sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge)

/-- 概要：全三因子表示の最終点は元の固定対象。
方針：元の coslice 辺の終点を全射として回収する。
規約：元の点射を変更しない。
使われ方：同じ対象上の slice への全 curry。 -/
lemma relativeSliceCoconeMap_right {K C : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ C}
    (a : K ⟶ sliceOver x) {d : (sliceUnder (a ≫ sliceOverProjection x)) _⦋0⦌}
    (e : (sliceUnder (a ≫ sliceOverProjection x)).Edge d (sliceDiagramCocone a)) :
    joinInr (join K Δ[0]) Δ[0] ≫ relativeSliceCoconeMap a e = x := by
  rw [relativeSliceCoconeMap, ← Category.assoc, joinAssociator_last, Category.assoc,
    ← Category.assoc (joinInr K _), joinInr_joinMap,
    Category.assoc, sliceUnderUncurry_projection, ← Category.assoc,
    joinStdSimplexIso_zero_inr,
    ← Category.assoc (SSet.stdSimplex.δ (0 : Fin 2)), e.δ_zero_yonedaEquiv_symm,
    SSet.yonedaEquiv_symm_comp]
  exact sliceDiagramCocone_point a

/-- 概要：元の全余錐への coslice 辺から同じ対象上の全余錐を構成する。
方針：全三因子射を curry して、元の図式への左制限を計算する。
規約：元の図式を全高次で厳密に保持する。
使われ方：filtered 表示段での μ-small 全図式の因子化。 -/
def relativeSliceCocone {K C : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ C}
    (a : K ⟶ sliceOver x) {d : (sliceUnder (a ≫ sliceOverProjection x)) _⦋0⦌}
    (e : (sliceUnder (a ≫ sliceOverProjection x)).Edge d (sliceDiagramCocone a)) :
    JoinCocone a :=
  ⟨sliceOverCurry (relativeSliceCoconeMap a e) (relativeSliceCoconeMap_right a e), by
    apply sliceOverUncurry_injective x
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry, relativeSliceCoconeMap,
      ← Category.assoc, joinAssociator_outerPair,
      ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.id_comp,
      joinStdSimplexIso_zero_inr, ← sliceUnderUncurry_precomp, e.δ_zero_yonedaEquiv_symm,
      sliceUnderUncurry_yoneda]
    rfl⟩

/-- 概要：相対全余錐の頂点の辺は元の coslice 辺の射影そのもの。
方針：頂点の全展開を join の右因子に制限して計算する。
規約：固定対象への全辺射の厳密な等式。
使われ方：元の指定表示脚での因子化の回収。 -/
lemma relativeSliceCocone_vertex_val {K C : SSet.{u}} {x : (Δ[0] : SSet.{u}) ⟶ C}
    (a : K ⟶ sliceOver x) {d : (sliceUnder (a ≫ sliceOverProjection x)) _⦋0⦌}
    (e : (sliceUnder (a ≫ sliceOverProjection x)).Edge d (sliceDiagramCocone a)) :
    (relativeSliceCocone a e).vertex.val =
      (edgeCosliceVertex (e.map (sliceUnderProjection (a ≫ sliceOverProjection x))).toTruncated).val := by
  rw [← sliceOverUncurry_yoneda 0 (relativeSliceCocone a e).vertex]
  rw [JoinCocone.vertex_eq, Equiv.symm_apply_apply, sliceOverUncurry_precomp]
  change joinMap (joinInr K Δ[0]) (𝟙 Δ[0]) ≫
    sliceOverUncurry (sliceOverCurry (relativeSliceCoconeMap a e)
      (relativeSliceCoconeMap_right a e)) = _
  rw [sliceOverUncurry_curry, relativeSliceCoconeMap,
    ← Category.assoc, joinAssociator_rightPair,
    ← Category.assoc (joinInr K _), joinInr_joinMap, Category.assoc,
    sliceUnderUncurry_projection, SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
