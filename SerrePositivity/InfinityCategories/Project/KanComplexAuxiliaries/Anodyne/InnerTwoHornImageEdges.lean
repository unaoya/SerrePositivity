module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Anodyne.InnerTwoHornEdges

/-!
概要：同型で表示した二次内ホーンの像で欠ける辺は、同じ長辺の像だけ。
方針：元の辺を同じ底同型で標準二単体へ戻し、既存の長辺判定を適用する。
規約：退化辺を含む全ての一次単体を扱う。
使われ方：通常圏の nerve 上の二次ホーンによる指定辺保存の反映。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-- 同型で表示した内ホーンの像にない辺は、同じ底同型による標準長辺の像。 -/
lemma innerTwoHorn_image_missing_edge_eq_long {B : SSet.{u}}
    (s : (Δ[2] : SSet.{u}) ≅ B) (e : B _⦋1⦌)
    (he : e ∉ Set.range (((horn 2 1).ι ≫ s.hom).app (Opposite.op ⦋1⦌))) :
    SSet.yonedaEquiv.symm e = stdSimplex.δ (1 : Fin 3) ≫ s.hom := by
  have hi : s.hom.app (Opposite.op ⦋1⦌) (s.inv.app (Opposite.op ⦋1⦌) e) = e :=
    congrArg (fun f : B ⟶ B ↦ f.app (Opposite.op ⦋1⦌) e) s.inv_hom_id
  have hm : s.inv.app (Opposite.op ⦋1⦌) e ∉ (horn 2 1).obj (Opposite.op ⦋1⦌) := by
    intro h
    exact he ⟨⟨s.inv.app (Opposite.op ⦋1⦌) e, h⟩, hi⟩
  have hl := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.innerTwoHorn_missing_edge_eq_long _ hm
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  exact hi.symm.trans (congrArg (s.hom.app (Opposite.op ⦋1⦌)) hl)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
