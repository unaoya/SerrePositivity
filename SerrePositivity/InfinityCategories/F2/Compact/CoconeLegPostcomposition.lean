module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationPointPost

/-!
概要：元の余錐脚の全一単体は、元の全余錐の後合成と厳密に可換。
方針：元の join 制限と Yoneda の後合成自然性で計算する。
規約：余錐・脚・後合成射を変更しない。使われ方：分類図式の実際の脚への輸送比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全余錐像の脚は、元の脚を同じ後合成射で写した全一単体を回収する。 -/
lemma coconeTransportLeg_post_edge {I X Y : SSet.{u}} {D : I ⟶ X}
    (G : X ⟶ Y) (c : JoinCocone D) (i : I _⦋0⦌) :
    (coconeTransportLeg (mapJoinCocone G c) i).edge =
      ((coconeTransportLeg c i).map G).edge := by
  rw [coconeTransportLeg_edge]
  change SSet.yonedaEquiv (_ ≫ _ ≫ (c.val ≫ G)) =
    G.app (Opposite.op ⦋1⦌) (coconeTransportLeg c i).edge
  rw [coconeTransportLeg_edge]
  change SSet.yonedaEquiv (_ ≫ _ ≫ (c.val ≫ G)) =
    G.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (_ ≫ _ ≫ c.val))
  rw [← SSet.yonedaEquiv_comp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Compact
