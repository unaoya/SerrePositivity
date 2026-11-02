module

public import SerrePositivity.InfinityCategories.F2.Filtered.KappaFilteredCoslices
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：元の coslice の全図式が κ-filtered な一段へ下りていれば、比較の引き戻し内に余錐を作れる。
方針：一段の coslice 内の余錐を全 join で後合成し、同じ元の固定点へ curry して戻す。
規約：元の図式を厳密に保つ。使われ方：全空間比較の coslice の filtered 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ κ-filtered な段へ下りた全 coslice 図式から、元の比較の引き戻し内の余錐を得る。 -/
lemma nonempty_coslicePullback_cocone_of_stage {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K W E Q : SSet.{u}} [Quasicategory Q] [IsKappaFiltered κ Q]
    (hK : IsKappaSmall κ K) (f : W ⟶ E) (p : (Δ[0] : SSet.{u}) ⟶ E)
    (s : Q ⟶ W) (l : Q ⟶ E) (hs : s ≫ f = l)
    (a : K ⟶ pullback f (sliceUnderProjection p))
    (h : join (Δ[0] : SSet.{u}) K ⟶ Q)
    (hh : h ≫ l = sliceUnderUncurry (a ≫ pullback.snd f (sliceUnderProjection p)))
    (ha : a ≫ pullback.fst f (sliceUnderProjection p) = (joinInr Δ[0] K ≫ h) ≫ s) :
    Nonempty (JoinCocone a) := by
  let q := joinInl (Δ[0] : SSet.{u}) K ≫ h
  let b := sliceUnderCurry h (show joinInl Δ[0] K ≫ h = q from rfl)
  have hq : q ≫ l = p := by
    dsimp only [q]
    rw [Category.assoc, hh, sliceUnderUncurry_fixed]
  obtain ⟨c⟩ := nonempty_cocone_in_kappaFiltered_coslice hκ
    (isKappaSmall_of_finite hκ.aleph0_le _) hK q b
  let cE := sliceUnderCurry (sliceUnderUncurry c.val ≫ l) (by
    rw [← Category.assoc, sliceUnderUncurry_fixed, hq])
  have hE : joinInl K Δ[0] ≫ cE = a ≫ pullback.snd f (sliceUnderProjection p) := by
    apply sliceUnderUncurry_injective
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry, ← Category.assoc,
      ← sliceUnderUncurry_precomp, c.property, sliceUnderUncurry_curry]
    exact hh
  have hp : cE ≫ sliceUnderProjection p = c.val ≫ sliceUnderProjection q ≫ l := by
    rw [sliceUnderCurry_projection, ← Category.assoc, sliceUnderUncurry_projection,
      Category.assoc]
  let cW := c.val ≫ sliceUnderProjection q ≫ s
  have hw : cW ≫ f = cE ≫ sliceUnderProjection p := by
    dsimp only [cW]
    rw [Category.assoc, Category.assoc, hs]
    exact hp.symm
  let d := pullback.lift cW cE hw
  refine ⟨⟨d, ?_⟩⟩
  apply pullback.hom_ext
  · change joinInl K Δ[0] ≫ d ≫ pullback.fst f (sliceUnderProjection p) = _
    dsimp only [d]
    rw [pullback.lift_fst]
    dsimp only [cW]
    rw [← Category.assoc, ← Category.assoc, c.property,
      sliceUnderCurry_projection]
    exact ha.symm
  · change joinInl K Δ[0] ≫ d ≫ pullback.snd f (sliceUnderProjection p) = _
    dsimp only [d]
    rw [pullback.lift_snd]
    exact hE

end SerrePositivity.InfinityCategories.F2.Ind
