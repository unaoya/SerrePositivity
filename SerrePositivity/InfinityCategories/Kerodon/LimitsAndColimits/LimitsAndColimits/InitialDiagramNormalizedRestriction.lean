module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramHomFamily

/-!
概要：部分図式の表示を正規化した場合も、同じ頂点の初期 Hom 族を厳密に回収する。
方針：二段の正規化制限を uncurry し、同じ頂点座標へ合成する。
規約：元の全図式族を保持。使われ方：付加辺面の両端を元の根辺の初期族へ同定する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {K L E B T : SSet.{u}} (q : E ⟶ B) (t : K ⟶ E) (i : L ⟶ K)
  (s : L ⟶ E) (ht : i ≫ t = s) (y : B _⦋0⦌)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t) (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) ≫ q = SSet.const y)

include ha in
/-- 正規化した部分図式への制限は、元の同じ終点 y 上に留まる。 -/
lemma initialDiagramNormalizedRestriction_fixed :
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction t i ht) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection s) ≫ q =
      SSet.const y := by
  rw [Category.assoc a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection]
  exact ha

/-- 正規化した部分図式の初期 Hom 族は、元の同じ頂点の族に厳密に一致する。 -/
lemma initialDiagramHomFamily_normalized_restrict (c : E _⦋0⦌)
    (v : (Δ[0] : SSet.{u}) ⟶ L) (w : (Δ[0] : SSet.{u}) ⟶ K) (hi : v ≫ i = w)
    (hv : v ≫ s = SSet.yonedaEquiv.symm c) (hw : w ≫ t = SSet.yonedaEquiv.symm c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c s v hv y (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction t i ht)
        (initialDiagramNormalizedRestriction_fixed q t i s ht y a ha) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t w hw y a ha := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (SSet.yonedaEquiv.symm c)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.comp_id, hi]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
