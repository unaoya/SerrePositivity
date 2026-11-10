module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightConeBoundary
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の単射に同じ右余錐点を付けた包含は right anodyne。
方針：right fibration の点 slice の後合成の自明 Kan 性へ持ち上げを移す。
規約：元の単射以外の仮定なし。使われ方：有限セルの余極限構成における、共通の右余錐点を保つ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の右余錐の頂点包含は right anodyne。 -/
lemma rightConeTip_rightAnodyne (A : SSet.{u}) :
    rightAnodyneExtensions (joinInr A (Δ[0] : SSet.{u})) := by
  intro E B p hp
  have : RightFibration p := ⟨hp⟩
  constructor
  intro u v sq
  have := HomotopyLimits.sliceOverPostcomp_trivialKanFibration_of_rightFibration u p
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (sliceOverPostcomp u p)
  let w := sliceOverCurry v sq.w.symm
  refine CommSq.HasLift.mk' { l := sliceOverUncurry (w ≫ s), fac_left := ?_, fac_right := ?_ }
  · exact sliceOverUncurry_fixed _
  · have he : (w ≫ s) ≫ sliceOverPostcomp u p = w := by
      rw [Category.assoc, hs, Category.comp_id]
    have h := congrArg sliceOverUncurry he
    rw [sliceOverUncurry_postcomp] at h
    exact h.trans (sliceOverUncurry_curry v sq.w.symm)

/-- 同じ右余錐点を保つ任意の単射の拡大は、right fibration に対して持ち上がる。 -/
@[kerodon 0196]
lemma joinPoint_mono_rightAnodyne {A T : SSet.{u}} (i : A ⟶ T) [Mono i] :
    rightAnodyneExtensions (joinMap i (𝟙 (Δ[0] : SSet.{u}))) := by
  intro E B p hp
  have : RightFibration p := ⟨hp⟩
  constructor
  intro u v sq
  let c := joinInr A (Δ[0] : SSet.{u}) ≫ u
  have hv : joinInr T (Δ[0] : SSet.{u}) ≫ v = c ≫ p := by
    have h := congrArg (fun f => joinInr A (Δ[0] : SSet.{u}) ≫ f) sq.w
    simpa only [c, ← Category.assoc, joinInr_joinMap, Category.id_comp] using h.symm
  have := HomotopyLimits.sliceOverPostcomp_trivialKanFibration_of_rightFibration c p
  have := TrivialKanFibration.mem (p := sliceOverPostcomp c p) i inferInstance
  have hs : CommSq (sliceOverCurry u (show joinInr A Δ[0] ≫ u = c from rfl)) i
      (sliceOverPostcomp c p) (sliceOverCurry v hv) := by
    constructor
    apply sliceOverUncurry_injective (c ≫ p)
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp,
      sliceOverUncurry_curry, sliceOverUncurry_curry]
    exact sq.w
  refine CommSq.HasLift.mk' { l := sliceOverUncurry hs.lift, fac_left := ?_, fac_right := ?_ }
  · have h := congrArg sliceOverUncurry hs.fac_left
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry] at h
    exact h
  · have h := congrArg sliceOverUncurry hs.fac_right
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry] at h
    exact h

end SerrePositivity.InfinityCategories
