module
public import SerrePositivity.KST.SConstruction.EndpointFixedDiamondComparison
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders

/-! # 定数三辺の実三角形対を同じ頂点へ表示移送
概要：三辺が定数である実三角形対を、全二単体を変えず同じ頂点の二三角形へ移す。
方針：元の全辺の定数性から頂点の等号を回収し、元の三角形を表示移送する。
規約：全二単体と生成第四辺全体の等号を同じデータに保存する。
使われ方：零段の三つの定数 BF 辺と生成第四辺の全端点固定比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の全辺の後合成が定数なら、同じ写像で写した全辺も定数。 -/
lemma constantEdge_map {E B : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y) (p : E ⟶ B)
    (h : ∃ v, SSet.yonedaEquiv.symm a.edge ≫ p = SSet.const v) :
    ∃ v, SSet.yonedaEquiv.symm (a.map p).edge = SSet.const v := by
  simpa only [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp] using h

/-- 全辺が定数なら、その始点と終点は同じ元の頂点。 -/
lemma constantEdge_endpoints {E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y)
    (h : ∃ v, SSet.yonedaEquiv.symm a.edge = SSet.const v) : x = y := by
  obtain ⟨v, hv⟩ := h
  have he : a.edge = (SSet.Edge.id v).edge :=
    SSet.yonedaEquiv.symm.injective (hv.trans (mappingIdentityEdge_map v).symm)
  have hs : x = v := a.src_eq.symm.trans
    ((congrArg (E.δ 1) he).trans (SSet.Edge.id v).src_eq)
  have ht : y = v := a.tgt_eq.symm.trans
    ((congrArg (E.δ 0) he).trans (SSet.Edge.id v).tgt_eq)
  exact hs.trans ht.symm

/-- 定数な元の全辺は、同じ元の始点の定数区間そのもの。 -/
lemma constantEdge_source {E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y)
    (h : ∃ v, SSet.yonedaEquiv.symm a.edge = SSet.const v) :
    SSet.yonedaEquiv.symm a.edge = SSet.const x := by
  obtain ⟨v, hv⟩ := h
  have he : a.edge = (SSet.Edge.id v).edge :=
    SSet.yonedaEquiv.symm.injective (hv.trans (mappingIdentityEdge_map v).symm)
  have hs : x = v := a.src_eq.symm.trans
    ((congrArg (E.δ 1) he).trans (SSet.Edge.id v).src_eq)
  exact hv.trans (congrArg SSet.const hs.symm)

/-- 定数な元の全辺は、同じ元の終点の定数区間でもある。 -/
lemma constantEdge_target {E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y)
    (h : ∃ v, SSet.yonedaEquiv.symm a.edge = SSet.const v) :
    SSet.yonedaEquiv.symm a.edge = SSet.const y :=
  (constantEdge_source a h).trans (congrArg SSet.const (constantEdge_endpoints a h))

/-- 定数三辺の二三角形を同じ始点へ移し、元の第四辺・両全三角形を厳密に保存する。 -/
def constantDiamondAtSourceData {E : SSet.{u}} {x m n z : E _⦋0⦌}
    {a : E.Edge x m} {b : E.Edge m z} {c e : E.Edge x n} {d : E.Edge n z}
    (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a b c d)
    (ha : ∃ v, SSet.yonedaEquiv.symm a.edge = SSet.const v)
    (hb : ∃ v, SSet.yonedaEquiv.symm b.edge = SSet.const v)
    (hd : ∃ v, SSet.yonedaEquiv.symm d.edge = SSet.const v)
    (he : ∃ v, SSet.yonedaEquiv.symm e.edge = SSet.const v) :
    Σ c' : E.Edge x x,
      {D' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond (SSet.Edge.id x) (SSet.Edge.id x) c' (SSet.Edge.id x) //
        c'.edge = c.edge ∧ D'.first.simplex = D.first.simplex ∧
          D'.second.simplex = D.second.simplex} := by
  have hm : m = x := (constantEdge_endpoints a ha).symm
  have hz : z = x := (constantEdge_endpoints b hb).symm.trans hm
  have hn : n = x := (constantEdge_endpoints e he).symm
  let c' := c.ofEq rfl hn
  let diagonal := D.diagonal.ofEq rfl hz
  have ha' : a.edge = (SSet.Edge.id x).edge :=
    SSet.yonedaEquiv.symm.injective
      ((constantEdge_source a ha).trans (mappingIdentityEdge_map x).symm)
  have hb' : b.edge = (SSet.Edge.id x).edge :=
    SSet.yonedaEquiv.symm.injective
      (((constantEdge_source b hb).trans (congrArg SSet.const hm)).trans
        (mappingIdentityEdge_map x).symm)
  have hd' : d.edge = (SSet.Edge.id x).edge :=
    SSet.yonedaEquiv.symm.injective
      (((constantEdge_target d hd).trans (congrArg SSet.const hz)).trans
        (mappingIdentityEdge_map x).symm)
  exact ⟨c', ⟨⟨diagonal, D.first.ofEq ha' hb' rfl, D.second.ofEq rfl hd' rfl⟩,
    rfl, rfl, rfl⟩⟩

end SerrePositivity.KST.SConstruction
