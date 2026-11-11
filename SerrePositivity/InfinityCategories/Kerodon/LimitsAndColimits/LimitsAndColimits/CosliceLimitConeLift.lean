module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorInclusions
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits

/-!
概要：coslice の図式の底にある極限錐を同じ全射を保って持ち上げる。
方針：底の錐の圏で元の点錐から極限錐への辺を取り、join を再結合する。
規約：図式の形状は任意、元の底の全錐を厳密に保持する。
使われ方：随伴関手定理の解対象を構成する極限錐の持ち上げ。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {K X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X} (D : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)

/-- 概要：coslice の図式は固定点を頂点とする底の錐を与える。
方針：元の全図式を uncurry する。
規約：元の固定点 p を保持する。
使われ方：極限錐への射の始点。 -/
def cosliceDiagramBaseCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry D, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection D⟩

/-- 概要：底の錐の辺を coslice の錐の全展開へ再結合する。
方針：二点の join を標準辺に同定し、二つの錐頂点を順に読む。
規約：元の辺の全高次単体を使う。
使われ方：底の極限錐の持ち上げの全射。 -/
def cosliceConeRaw (s : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator Δ[0] Δ[0] K).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom (𝟙 K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s

/-- 概要：始端が元の点錐なら再結合した射の外側の面は元の coslice 図式。
方針：結合同型の外側二因子の面を標準辺の始端へ移す。
規約：元の始端条件を全錐の等式で要求する。
使われ方：持ち上げた錐の図式制限の検査。 -/
lemma cosliceConeRaw_outer
    (s : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) ≫ cosliceConeRaw D s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry D := by
  unfold cosliceConeRaw
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_inv_outerPair, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, Category.id_comp,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
  rfl

/-- 概要：再結合した射は元の coslice の固定点を保つ。
方針：外側の図式面のさらに最初の頂点へ制限する。
規約：任意の同型な点へ変更しない。
使われ方：全射を coslice へ curry する固定条件。 -/
lemma cosliceConeRaw_fixed
    (s : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) ≫ cosliceConeRaw D s = p := by
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) ≫
          cosliceConeRaw D s) := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    _ = _ := by rw [cosliceConeRaw_outer D s hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]

/-- 概要：底の錐の辺から元の coslice 図式の全錐を構成する。
方針：再結合した全射を固定点について curry する。
規約：元の図式 D を厳密に制限として保持する。
使われ方：極限錐の持ち上げの構成。 -/
def cosliceConeOfBaseEdge
    (s : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (cosliceConeRaw D s) (cosliceConeRaw_fixed D s hs), by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective p
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
    exact cosliceConeRaw_outer D s hs⟩

/-- 概要：持ち上げた錐の底の全射は元の辺の終端錐と一致する。
方針：結合同型の後二因子の面を標準辺の終端へ移す。
規約：元の全錐 c の射そのものを回収する。
使われ方：指定した極限錐と持ち上げの照合。 -/
lemma cosliceConeOfBaseEdge_projection
    (s : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))
    (ht : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm c) :
    (cosliceConeOfBaseEdge D s hs).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = c.val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (cosliceConeRaw D s)
      (cosliceConeRaw_fixed D s hs)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]
  unfold cosliceConeRaw
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_inv_rightPair, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr, Category.id_comp,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]

/-- 概要：coslice の図式の底の極限錐は同じ全射を持つ coslice の錐へ持ち上がる。
方針：底の錐の圏の終対象性で元の点錐からの辺を選び、その全射を再結合する。
規約：持ち上げの極限性は仮定も主張もせず、必要な全錐の存在を構成する。
使われ方：小さい解図式の極限から点付きの解対象を得る工程。 -/
lemma exists_cosliceCone_lift_of_isLimit (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) : ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D, d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = c.val := by
  obtain ⟨e⟩ := hc.nonempty_edge (cosliceDiagramBaseCone D)
  let s : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) :=
    SSet.yonedaEquiv.symm e.edge
  have hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D) := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    simp only [s, Equiv.apply_symm_apply]
    exact e.src_eq
  have ht : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm c := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    simp only [s, Equiv.apply_symm_apply]
    exact e.tgt_eq
  exact ⟨cosliceConeOfBaseEdge D s hs, cosliceConeOfBaseEdge_projection D s hs c ht⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
