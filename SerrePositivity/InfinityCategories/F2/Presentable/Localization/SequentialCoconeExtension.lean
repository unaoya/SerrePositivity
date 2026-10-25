module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeNestedCosliceProjection

/-!
概要：全余錐間の指定辺から、次の頂点を付加した図式の同じ大域余錐を作る。
方針：公開された二重 coslice 同型の逆を使い、元の全余錐と辺を回収する。
規約：旧段階への全制限と新頂点からの指定辺を厳密に保つ。
使われ方：HTT 5.5.4.13 の相対因子化を coherent な交互列へ組み込む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {K C : SSet.{u}} {p : K ⟶ C} {w z : JoinCocone p}
  (k : (sliceUnder p).Edge w z)

/-- 次の頂点を持つ全図式 w の下に、元の指定辺から大域余錐を付加する。 -/
def sequentialCoconeExtension : JoinCocone w.val :=
  (nestedCosliceIso w).inv.app _ (edgeCosliceVertex k.toTruncated)

/-- 次段階の大域余錐を旧図式へ戻すと、元の同じ全余錐になる。 -/
lemma sequentialCoconeExtension_target :
    coconeComparisonTarget w (sequentialCoconeExtension k) = z := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (coconeNestedCoslice_inv_restriction w) (Opposite.op ⦋0⦌))
    (edgeCosliceVertex k.toTruncated)
  change (colimitCosliceRestriction w).app _
    ((nestedCosliceIso w).inv.app _ (edgeCosliceVertex k.toTruncated)) =
      (sliceUnderProjection (SSet.yonedaEquiv.symm w)).app _
        (edgeCosliceVertex k.toTruncated) at h
  rw [edgeCosliceVertex_projection] at h
  exact h

/-- 旧段階の全余錐の射は、追加後も厳密に同じ値を持つ。 -/
lemma sequentialCoconeExtension_restrict_val :
    ((sequentialCoconeExtension k).restrict (joinInl K Δ[0])).val = z.val := by
  have h := (coconeComparisonTarget_eq w (sequentialCoconeExtension k)).symm.trans
    (sequentialCoconeExtension_target k)
  have hv := congrArg (fun c : JoinCocone p ↦ c.val) h
  rwa [coherentCoconeOfDiagramEq_val] at hv

/-- 大域余錐の頂点も元の指定頂点である。 -/
lemma sequentialCoconeExtension_vertex : (sequentialCoconeExtension k).vertex = z.vertex :=
  (coconeComparisonTarget_vertex w (sequentialCoconeExtension k)).symm.trans
    (congrArg JoinCocone.vertex (sequentialCoconeExtension_target k))

/-- 次段階から回収した余錐間の比較辺は、元の指定辺そのものである。 -/
lemma sequentialCoconeExtension_comparison_edge :
    (coconeComparisonEdge w (sequentialCoconeExtension k)).edge = k.edge := by
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Iso.inv_hom_id (nestedCosliceIso w)) (Opposite.op ⦋0⦌))
    (edgeCosliceVertex k.toTruncated)
  change (nestedCosliceIso w).hom.app _
    ((nestedCosliceIso w).inv.app _ (edgeCosliceVertex k.toTruncated)) =
      edgeCosliceVertex k.toTruncated at hn
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((nestedCosliceIso w).hom.app _ (sequentialCoconeExtension k)).val) = k.edge
  rw [show (nestedCosliceIso w).hom.app _ (sequentialCoconeExtension k) =
    edgeCosliceVertex k.toTruncated from hn]
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm k.edge)) = k.edge
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 新頂点から大域頂点への脚は、指定辺を終域射影した同じ辺である。 -/
lemma sequentialCoconeExtension_leg :
    ((sequentialCoconeExtension k).leg (joinInr K Δ[0])).edge =
      (k.map (sliceUnderProjection p)).edge := by
  have h := coconeComparisonEdge_projection w (sequentialCoconeExtension k)
  change (sliceUnderProjection p).app _
    (coconeComparisonEdge w (sequentialCoconeExtension k)).edge = _ at h
  rw [sequentialCoconeExtension_comparison_edge] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
