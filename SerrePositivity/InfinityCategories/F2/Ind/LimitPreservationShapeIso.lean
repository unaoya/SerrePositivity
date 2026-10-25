module

public import SerrePositivity.InfinityCategories.F2.Ind.LimitPreservationOpposite
public import SerrePositivity.InfinityCategories.Stable.ReindexSliceOver

/-!
概要：形状同型に沿い、元の関手による全極限錐の保存を輸送する。
方針：元の錐と像の錐を同じ形状へ制限し、全射の合成式で照合する。
規約：元の全錐を保持し、形状の宇宙はここでは変えない。
使われ方：I-2 d′ の小さい基底形状から大きい有限生成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 全極限錐の保存は、元の形状の厳密な同型によって移る。 -/
lemma map_isLimit_of_shapeIso {A K X Y : SSet.{u}} (U : X ⟶ Y) (e : A ≅ K)
    (hU : ∀ (p : A ⟶ X) (c : JoinCone p), IsLimitCone c → IsLimitCone (mapJoinCone U c))
    {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone U c) := by
  have h := hU _ (c.reindexIso e) ((isLimitCone_iff_reindexIso c e).mp hc)
  apply (isLimitCone_iff_reindexIso (mapJoinCone U c) e).mpr
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).mp h
  change (joinMap (𝟙 (Δ[0] : SSet.{u})) e.hom ≫ c.val) ≫ U =
    joinMap (𝟙 (Δ[0] : SSet.{u})) e.hom ≫ (c.val ≫ U)
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
