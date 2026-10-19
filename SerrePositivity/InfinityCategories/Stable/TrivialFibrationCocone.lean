module
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits

/-! # 自明 Kan fibration に沿う余極限の保存と反映

概要：coslice の後合成も自明 Kan fibration であり、余極限性を保ち反映する。
方針：相対境界充填を join の単射に移し、同値による始対象の判定を使う。
規約：任意の図式の形状を扱う。使われ方：β3 の dg 模型間の安定性の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 自明 Kan fibration による coslice の後合成も自明 Kan fibration。 -/
instance trivialKanFibration_sliceUnderPostcomp {K E B : SSet.{u}} (p : K ⟶ E) (q : E ⟶ B)
    [TrivialKanFibration q] : TrivialKanFibration (sliceUnderPostcomp p q) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let i := joinMap (𝟙 K) (boundary n).ι
  have hm : Mono i := joinMap_mono _ _
  have := TrivialKanFibration.mem (p := q) i hm
  have hw := congrArg (fun F => sliceUnderUncurry F) sq.w
  rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at hw
  have s : CommSq (sliceUnderUncurry a) i q (sliceUnderUncurry b) := ⟨hw⟩
  have hK : joinInl K (Δ[n] : SSet.{u}) ≫ s.lift = p := by
    have h := congrArg (fun F => joinInl K (boundary n : SSet.{u}) ≫ F) s.fac_left
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' {
    l := sliceUnderCurry s.lift hK
    fac_left := ?_
    fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact s.fac_left
  · apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    exact s.fac_right

/-- 自明 Kan fibration で余錐を後合成する。 -/
def mapJoinCocone {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCocone p) :
    JoinCocone (p ≫ f) := ⟨c.val ≫ f, by rw [← Category.assoc, c.property]⟩

/-- 自明 Kan fibration は任意の図式の余極限性を保存し反映する。 -/
lemma isColimitCone_iff_mapJoinCocone_of_trivialKanFibration {K E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    {p : K ⟶ E} (c : JoinCocone p) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone q c) :=
  (qCatEquivalenceOfTrivialKanFibration (sliceUnderPostcomp p q)).isInitialVertex_iff c

end SerrePositivity.InfinityCategories
