module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomFamily

/-!
概要：部分図式から初期 Hom を読む操作を、元の同じ図式の初期頂点制限へ戻す。
方針：fiber の包含後に正規化した二段制限を uncurry し、頂点の座標を使う。
規約：元の全族を保持する。使われ方：長辺族と元の三角形・四面体の初期 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ初期頂点の座標を持つ二段制限は、固定終点の初期 Hom 族でも厳密に一致する。 -/
lemma initialDiagramHomFamily_restrict {K L E B T : SSet.{u}}
    (q : E ⟶ B) (c : E _⦋0⦌) (t : K ⟶ E) (i : L ⟶ K)
    (v : (Δ[0] : SSet.{u}) ⟶ L) (w : (Δ[0] : SSet.{u}) ⟶ K)
    (hi : v ≫ i = w) (hv : v ≫ (i ≫ t) = SSet.yonedaEquiv.symm c)
    (hw : w ≫ t = SSet.yonedaEquiv.symm c) (y : B _⦋0⦌)
    (a : T ⟶ sliceUnder t) (ha : (a ≫ sliceUnderProjection t) ≫ q = SSet.const y) :
    initialDiagramHomFamily q c (i ≫ t) v hv y (a ≫ sliceUnderRestrict t i)
        (by
          rw [Category.assoc a (sliceUnderRestrict t i) (sliceUnderProjection (i ≫ t)),
            sliceUnderRestrict_projection]
          exact ha) =
      initialDiagramHomFamily q c t w hw y a ha := by
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y
  rw [initialDiagramHomFamily, initialDiagramHomFamily, vertexFiberLift_ι, vertexFiberLift_ι]
  apply sliceUnderUncurry_injective (SSet.yonedaEquiv.symm c)
  rw [normalizedCoconeRestriction_uncurry, sliceUnderUncurry_restrict,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, hi]

end SerrePositivity.InfinityCategories.HomotopyLimits
