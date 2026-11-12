module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSlicePost
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSlicePrismReverse

/-!
概要：元の右 slice 後合成を、同じ正規化済みの反対左 coslice へ移す。
方針：既存の底上の slice 反転同型で共役し、元の実 prism の反転を保つ。
規約：元の全空間の射を保持。使われ方：指定対角比較の後合成自然性の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W : C}
local notation "z" => coherentNerveVertex Z
local notation "w" => coherentNerveVertex W

/-- 元の右 slice 後合成を同じ底上の反対左 coslice の射として保持する。 -/
def coherentReverseSlicePost (g : Z ⟶ W) :
    sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) ⟶
      sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)) :=
  (cofinalPointSliceOverOpIso z).inv.left ≫
    SSet.opFunctor.map (coherentRightSlicePost g) ≫ (cofinalPointSliceOverOpIso w).hom.left

/-- 元の反対左 coslice の後合成は、同じ反対 nerve への射影を厳密に保つ。 -/
lemma coherentReverseSlicePost_projection (g : Z ⟶ W) :
    coherentReverseSlicePost g ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)) =
      sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) := by
  have hw := (cofinalPointSliceOverOpIso w).hom.w
  change (cofinalPointSliceOverOpIso w).hom.left ≫
    sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)) =
      SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm w)) at hw
  dsimp only [coherentReverseSlicePost]
  rw [Category.assoc, Category.assoc, hw,
    ← SSet.opFunctor.map_comp, coherentRightSlicePost_projection]
  exact (cofinalPointSliceOverOpIso z).inv.w

/-- 元の正規化済み slice 反転と、指定後合成の反転は厳密に可換。 -/
lemma coherentReverseSlicePost_from_over (g : Z ⟶ W) :
    (cofinalPointSliceOverOpIso z).hom.left ≫ coherentReverseSlicePost g =
      SSet.opFunctor.map (coherentRightSlicePost g) ≫
        (cofinalPointSliceOverOpIso w).hom.left := by
  have hi : (cofinalPointSliceOverOpIso z).hom.left ≫
      (cofinalPointSliceOverOpIso z).inv.left = 𝟙 _ :=
    congrArg (fun k ↦ k.left) (Iso.hom_inv_id (cofinalPointSliceOverOpIso z))
  rw [coherentReverseSlicePost, ← Category.assoc, hi, Category.id_comp]

/-- 元の右 slice prism の反転は、同じ指定後合成の像の反転へ厳密に移る。 -/
lemma reversePointSlicePrism_coherent_post {A : SSet.{max u v}}
    (H : (Δ[1] : SSet.{max u v}) ⊗ A ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (g : Z ⟶ W) :
    reversePointSlicePrism z H ≫ coherentReverseSlicePost g =
      reversePointSlicePrism w (H ≫ coherentRightSlicePost g) := by
  dsimp only [reversePointSlicePrism]
  rw [Category.assoc, coherentReverseSlicePost_from_over, reversePrism_postcomp, Category.assoc]

end SerrePositivity.InfinityCategories.F2
