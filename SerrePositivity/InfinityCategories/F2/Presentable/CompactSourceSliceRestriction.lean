module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactSourceSlices
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactFunctorRestriction

/-!
概要：始域の compact 性を保つ全 slice 比較を compact 始域 slice へ制限する。
方針：始域射影との全射等式で compact 保存を移し、全部分複体の公開持ち上げを使う。
規約：固定対象の正規化は指定された比較射に含め、元の全比較を保つ。
使われ方：compact 成分 comma の実引き戻しの両脚。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：slice の始域 compact 条件は頂点同型で不変。
方針：同型を元の始域射影で写して compact 不変性を適用する。
規約：同じ元の固定対象を保つ。
使われ方：制限された slice 比較の同値持ち上げ。 -/
lemma compactSourceSlicePredicate_iff_vertexIso (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
    {v w : (sliceOver x) _⦋0⦌} (e : VertexIso v w) :
    Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app _ v) ↔
      Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app _ w) :=
  Compact.isKappaCompact_iff_of_iso (VertexIso.map e (sliceOverProjection x))

/-- 概要：全始域比較を持つ slice 射の compact 始域への制限。
方針：全射等式を各頂点で評価して元の compact 保存を使う。
規約：正規化された全 slice 射 r をそのまま制限する。
使われ方：compact 成分圏の引き戻し錐。 -/
def compactSourceSliceRestriction (μ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ C} {y : (Δ[0] : SSet.{u + 1}) ⟶ D}
    (G : C ⟶ D) (r : sliceOver x ⟶ sliceOver y)
    (hr : r ≫ sliceOverProjection y = sliceOverProjection x ≫ G)
    (hc : ∀ c, Compact.IsKappaCompact.{u, u + 1} μ c →
      Compact.IsKappaCompact.{u, u + 1} μ (G.app _ c)) :
    compactSourceSlice μ x ⟶ compactSourceSlice μ y :=
  fullSubcomplexLift
    (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection y).app _ v))
    ((fullSubcomplexOnVertices (sliceOver x)
      (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app _ v))).ι ≫ r)
    (fun v ↦ by
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌)) v.val
      change (sliceOverProjection y).app _ (r.app _ v.val) =
        G.app _ ((sliceOverProjection x).app _ v.val) at h
      change Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection y).app _ (r.app _ v.val))
      rw [h]
      exact hc _ (fullSubcomplexOnVertices_vertex v))

/-- 概要：compact 始域への制限は元の全 slice 比較への包含と可換。
方針：全部分持ち上げの包含公式。
規約：全射の厳密な等式。
使われ方：実引き戻しの制限判定。 -/
lemma compactSourceSliceRestriction_inclusion (μ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ C} {y : (Δ[0] : SSet.{u + 1}) ⟶ D}
    (G : C ⟶ D) (r : sliceOver x ⟶ sliceOver y)
    (hr : r ≫ sliceOverProjection y = sliceOverProjection x ≫ G)
    (hc : ∀ c, Compact.IsKappaCompact.{u, u + 1} μ c →
      Compact.IsKappaCompact.{u, u + 1} μ (G.app _ c)) :
    compactSourceSliceRestriction μ G r hr hc ≫
      (fullSubcomplexOnVertices (sliceOver y)
        (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection y).app _ v))).ι =
      (fullSubcomplexOnVertices (sliceOver x)
        (fun v ↦ Compact.IsKappaCompact.{u, u + 1} μ ((sliceOverProjection x).app _ v))).ι ≫ r :=
  fullSubcomplexLift_ι _ _ _

/-- 概要：元の slice 比較の同値持ち上げ性は compact 始域への制限にも移る。
方針：始域 compact 条件の同型不変性と全部分制限の一般判定を使う。
規約：元の r の持ち上げ性と元の G の compact 保存を明示する。
使われ方：compact comma の厳密な引き戻しの小模型。 -/
lemma compactSourceSliceRestriction_equivalenceLifting (μ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ C} {y : (Δ[0] : SSet.{u + 1}) ⟶ D}
    (G : C ⟶ D) (r : sliceOver x ⟶ sliceOver y)
    (hr : r ≫ sliceOverProjection y = sliceOverProjection x ≫ G)
    (hc : ∀ c, Compact.IsKappaCompact.{u, u + 1} μ c →
      Compact.IsKappaCompact.{u, u + 1} μ (G.app _ c)) (hp : F1B.EquivalenceLifting r) :
    F1B.EquivalenceLifting (compactSourceSliceRestriction μ G r hr hc) :=
  kanEquivalenceLifting_fullRestriction _
    (fun e ↦ compactSourceSlicePredicate_iff_vertexIso μ x e) _ _ r
    (compactSourceSliceRestriction_inclusion μ G r hr hc) hp

end SerrePositivity.InfinityCategories.F2.Presentable
