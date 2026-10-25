module

public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeSliceCocone
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedFaces

/-!
概要：既存の固定標的上の相対余錐の全射影を回収する。
方針：元の三因子表示を、同じ coslice 辺の始点へ制限する。
規約：既存の relativeSliceCocone を使用し、構成を複製しない。
使われ方：長さ κ₀ の相対交互構成で一頂点を追加する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：固定標的上の新しい相対余錐の底図式は、元の選んだ全前置余錐そのもの。
方針：三因子表示を最初の二因子へ制限して、元の比較辺の始点を回収する。
規約：元の全図式を厳密な等式で返す。
使われ方：一頂点追加での元の compact 比較図式の回収。 -/
lemma relativeSliceCocone_projection {K X : SSet.{u}}
    {x : (Δ[0] : SSet.{u}) ⟶ X} (F : K ⟶ sliceOver x)
    {w : (sliceUnder (F ≫ sliceOverProjection x)) _⦋0⦌}
    (k : (sliceUnder (F ≫ sliceOverProjection x)).Edge w (sliceDiagramCocone F)) :
    (relativeSliceCocone F k).val ≫ sliceOverProjection x = w.val := by
  rw [relativeSliceCocone, sliceOverCurry_projection, relativeSliceCoconeMap]
  rw [← Category.assoc, joinAssociator_leftPair]
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
    joinStdSimplexIso_zero_inl, ← sliceUnderUncurry_precomp, k.δ_one_yonedaEquiv_symm,
    sliceUnderUncurry_yoneda]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
