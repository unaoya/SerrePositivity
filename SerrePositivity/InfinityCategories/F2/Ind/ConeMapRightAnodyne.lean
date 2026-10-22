module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightConeBoundary

/-!
概要：任意の単射に同じ右余錐点を付けた包含は right anodyne。
方針：right fibration の点 slice の後合成の自明 Kan 性へ持ち上げを移す。
規約：元の単射以外の仮定なし。使われ方：元の全終端辺を固定した相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ右余錐点を保つ任意の単射の拡大は、right fibration に対して持ち上がる。 -/
lemma coneMap_rightAnodyne {A T : SSet.{u}} (i : A ⟶ T) [Mono i] :
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

end SerrePositivity.InfinityCategories.F2.Ind
