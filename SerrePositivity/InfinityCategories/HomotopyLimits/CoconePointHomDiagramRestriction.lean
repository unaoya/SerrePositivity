module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomDiagramFamily

/-!
概要：元の普遍全 Hom 族の部分図式族をさらに制限し、同じ合成形状の族へ戻す。
方針：正規化制限の合成式を、同じ選択済みの全余錐族に前合成する。
規約：形状の厳密な合成式を要求。使われ方：native span の左右で共通する根辺族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K L M X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCocone p)
  (i : L ⟶ join K (Δ[0] : SSet.{u})) (s : L ⟶ X) (hs : i ≫ c.val = s)
  (j : M ⟶ L) (t : M ⟶ X) (hj : j ≫ s = t) (w : M ⟶ join K Δ[0])
  (hw : j ≫ i = w) (ht : w ≫ c.val = t) (y : X _⦋0⦌)

include hw

/-- 同じ普遍全族の二段の部分図式制限は、合成した同じ形状の制限そのもの。 -/
lemma coconePointHomDiagramFiberFamily_restrict :
    coconePointHomDiagramFiberFamily c i s hs y ≫
        normalizedCoconeRestrictionFiber s j hj y =
      coconePointHomDiagramFiberFamily c w t ht y := by
  exact (Category.assoc (coconePointFullHomFiberFamily c y)
    (normalizedCoconeRestrictionFiber c.val i hs y)
    (normalizedCoconeRestrictionFiber s j hj y)).trans
      (congrArg (coconePointFullHomFiberFamily c y ≫ ·)
        (normalizedCoconeRestrictionFiber_twoStep c.val i s hs j t hj w hw ht y))

end SerrePositivity.InfinityCategories.HomotopyLimits
