module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinAssociatorInclusions
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits

/-!
概要：coslice の図式の底にある極限錐を同じ全射を保って持ち上げる。
方針：底の錐の圏で元の点錐から極限錐への辺を取り、join を再結合する。
規約：図式の形状は任意、元の底の全錐を厳密に保持する。
使われ方：随伴関手定理の解対象を構成する極限錐の持ち上げ。
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
variable {K X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X} (D : K ⟶ sliceUnder p)

/-- 概要：coslice の図式は固定点を頂点とする底の錐を与える。
方針：元の全図式を uncurry する。
規約：元の固定点 p を保持する。
使われ方：極限錐への射の始点。 -/
def cosliceDiagramBaseCone : JoinCone (D ≫ sliceUnderProjection p) :=
  ⟨sliceUnderUncurry D, sliceUnderUncurry_projection D⟩

/-- 概要：底の錐の辺を coslice の錐の全展開へ再結合する。
方針：二点の join を標準辺に同定し、二つの錐頂点を順に読む。
規約：元の辺の全高次単体を使う。
使われ方：底の極限錐の持ち上げの全射。 -/
def cosliceConeRaw (s : (Δ[1] : SSet.{u}) ⟶ sliceOver (D ≫ sliceUnderProjection p)) :
    join (Δ[0] : SSet.{u}) (join (Δ[0] : SSet.{u}) K) ⟶ X :=
  (joinAssociator Δ[0] Δ[0] K).inv ≫
    joinMap (joinStdSimplexIso 0 0).hom (𝟙 K) ≫ sliceOverUncurry s

/-- 概要：始端が元の点錐なら再結合した射の外側の面は元の coslice 図式。
方針：結合同型の外側二因子の面を標準辺の始端へ移す。
規約：元の始端条件を全錐の等式で要求する。
使われ方：持ち上げた錐の図式制限の検査。 -/
lemma cosliceConeRaw_outer
    (s : (Δ[1] : SSet.{u}) ⟶ sliceOver (D ≫ sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D)) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (joinInr (Δ[0] : SSet.{u}) K) ≫ cosliceConeRaw D s =
      sliceUnderUncurry D := by
  unfold cosliceConeRaw
  rw [← Category.assoc, joinAssociator_inv_outerPair, ← Category.assoc,
    ← joinMap_comp, joinStdSimplexIso_zero_inl, Category.id_comp,
    ← sliceOverUncurry_precomp, hs, sliceOverUncurry_yoneda]
  rfl

/-- 概要：再結合した射は元の coslice の固定点を保つ。
方針：外側の図式面のさらに最初の頂点へ制限する。
規約：任意の同型な点へ変更しない。
使われ方：全射を coslice へ curry する固定条件。 -/
lemma cosliceConeRaw_fixed
    (s : (Δ[1] : SSet.{u}) ⟶ sliceOver (D ≫ sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D)) :
    joinInl (Δ[0] : SSet.{u}) (join (Δ[0] : SSet.{u}) K) ≫ cosliceConeRaw D s = p := by
  calc
    _ = joinInl (Δ[0] : SSet.{u}) K ≫
        (joinMap (𝟙 (Δ[0] : SSet.{u})) (joinInr (Δ[0] : SSet.{u}) K) ≫
          cosliceConeRaw D s) := by
      rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
    _ = _ := by rw [cosliceConeRaw_outer D s hs, sliceUnderUncurry_fixed]

/-- 概要：底の錐の辺から元の coslice 図式の全錐を構成する。
方針：再結合した全射を固定点について curry する。
規約：元の図式 D を厳密に制限として保持する。
使われ方：極限錐の持ち上げの構成。 -/
def cosliceConeOfBaseEdge
    (s : (Δ[1] : SSet.{u}) ⟶ sliceOver (D ≫ sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D)) :
    JoinCone D :=
  ⟨sliceUnderCurry (cosliceConeRaw D s) (cosliceConeRaw_fixed D s hs), by
    apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact cosliceConeRaw_outer D s hs⟩

/-- 概要：持ち上げた錐の底の全射は元の辺の終端錐と一致する。
方針：結合同型の後二因子の面を標準辺の終端へ移す。
規約：元の全錐 c の射そのものを回収する。
使われ方：指定した極限錐と持ち上げの照合。 -/
lemma cosliceConeOfBaseEdge_projection
    (s : (Δ[1] : SSet.{u}) ⟶ sliceOver (D ≫ sliceUnderProjection p))
    (hs : stdSimplex.δ 1 ≫ s = SSet.yonedaEquiv.symm (cosliceDiagramBaseCone D))
    (c : JoinCone (D ≫ sliceUnderProjection p))
    (ht : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm c) :
    (cosliceConeOfBaseEdge D s hs).val ≫ sliceUnderProjection p = c.val := by
  rw [← sliceUnderUncurry_projection]
  change joinInr (Δ[0] : SSet.{u}) (join (Δ[0] : SSet.{u}) K) ≫
    sliceUnderUncurry (sliceUnderCurry (cosliceConeRaw D s)
      (cosliceConeRaw_fixed D s hs)) = _
  rw [sliceUnderUncurry_curry]
  unfold cosliceConeRaw
  rw [← Category.assoc, joinAssociator_inv_rightPair, ← Category.assoc,
    ← joinMap_comp, joinStdSimplexIso_zero_inr, Category.id_comp,
    ← sliceOverUncurry_precomp, ht, sliceOverUncurry_yoneda]

/-- 概要：coslice の図式の底の極限錐は同じ全射を持つ coslice の錐へ持ち上がる。
方針：底の錐の圏の終対象性で元の点錐からの辺を選び、その全射を再結合する。
規約：持ち上げの極限性は仮定も主張もせず、必要な全錐の存在を構成する。
使われ方：小さい解図式の極限から点付きの解対象を得る工程。 -/
lemma exists_cosliceCone_lift_of_isLimit (c : JoinCone (D ≫ sliceUnderProjection p))
    (hc : IsLimitCone c) : ∃ d : JoinCone D, d.val ≫ sliceUnderProjection p = c.val := by
  obtain ⟨e⟩ := hc.nonempty_edge (cosliceDiagramBaseCone D)
  let s : (Δ[1] : SSet.{u}) ⟶ sliceOver (D ≫ sliceUnderProjection p) :=
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

end SerrePositivity.InfinityCategories.F2.Presentable
