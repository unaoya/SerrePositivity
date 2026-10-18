module
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-! # Trivial Kan fibration による任意図式の coslice の後合成

概要：trivial Kan fibration による後合成は任意の固定図式の coslice でも trivial Kan fibration となる。
方針：境界の持ち上げを join の単射の持ち上げへ移す。
規約：図式・値域に quasicategory 性を仮定しない。使われ方：始対象の下の図式の余錐の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：trivial Kan fibration の後合成は任意の図式の coslice で trivial Kan fibration を与える。
方針：余錐を uncurry し、右因子の境界包含との join に沿って持ち上げる。
規約：点の図式に制限しない。使われ方：始対象の coslice 射影による条件の消去。 -/
lemma sliceUnderPostcomp_trivialKanFibration_of_trivial {K E B : SSet.{u}}
    (p : K ⟶ E) (q : E ⟶ B) [TrivialKanFibration q] :
    TrivialKanFibration (sliceUnderPostcomp p q) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let j := joinMap (𝟙 K) (boundary n).ι
  have hj : Mono j := by dsimp [j]; infer_instance
  have := TrivialKanFibration.mem (p := q) j hj
  have hs : CommSq (sliceUnderUncurry a) j q (sliceUnderUncurry b) := by
    constructor
    have h := congrArg sliceUnderUncurry sq.w
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at h
    exact h
  let F := hs.lift
  have hfixed : joinInl K Δ[n] ≫ F = p := by
    have h := congrArg (fun f => joinInl K (boundary n : SSet.{u}) ≫ f) hs.fac_left
    change joinInl K (boundary n : SSet.{u}) ≫ (j ≫ F) = _ at h
    dsimp only [j] at h
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry F hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hs.fac_left
  · apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    exact hs.fac_right

end SerrePositivity.InfinityCategories
