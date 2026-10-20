module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramNormalizedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber

/-!
概要：正規化した二段の余錐制限を、同じ合成形状による制限へ厳密に同定する。
方針：uncurry して joinMap の合成則を使い、固定終点 fiber の包含で戻す。
規約：図式と形状の厳密な式を要求。使われ方：native な部分図式族の終端係数の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K L M X T : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K) (s : L ⟶ X) (hi : i ≫ p = s)
  (j : M ⟶ L) (t : M ⟶ X) (hj : j ≫ s = t) (w : M ⟶ K) (hw : j ≫ i = w)
  (ht : w ≫ p = t)

include hw

/-- 全パラメータの正規化した二段制限は、元の同じ合成形状の制限である。 -/
lemma normalizedCoconeRestriction_twoStep_family (a : T ⟶ sliceUnder p) :
    (a ≫ normalizedCoconeRestriction p i hi) ≫ normalizedCoconeRestriction s j hj =
      a ≫ normalizedCoconeRestriction p w ht := by
  apply sliceUnderUncurry_injective t
  rw [normalizedCoconeRestriction_uncurry, normalizedCoconeRestriction_uncurry,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, hw]

/-- 正規化した二段の制限写像そのものも、合成形状の制限に厳密に一致する。 -/
lemma normalizedCoconeRestriction_twoStep :
    normalizedCoconeRestriction p i hi ≫ normalizedCoconeRestriction s j hj =
      normalizedCoconeRestriction p w ht := by
  simpa only [Category.id_comp] using
    normalizedCoconeRestriction_twoStep_family p i s hi j t hj w hw ht (𝟙 (sliceUnder p))

/-- 固定終点 fiber の正規化した二段制限も、同じ合成形状の制限そのものである。 -/
lemma normalizedCoconeRestrictionFiber_twoStep (y : X _⦋0⦌) :
    normalizedCoconeRestrictionFiber p i hi y ≫ normalizedCoconeRestrictionFiber s j hj y =
      normalizedCoconeRestrictionFiber p w ht y := by
  apply vertexFiber_hom_ext (sliceUnderProjection t) y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  simp only [← Category.assoc, vertexFiberMap_ι]
  simpa only [Category.assoc] using congrArg (vertexFiberι (sliceUnderProjection p) y ≫ ·)
    (normalizedCoconeRestriction_twoStep p i s hi j t hj w hw ht)

end SerrePositivity.InfinityCategories.HomotopyLimits
