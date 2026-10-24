module

public import SerrePositivity.InfinityCategories.Core.ConeAnodyne
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：任意の図式の slice による自明 Kan fibration の保存。
方針：slice の境界充填を join の単射に対する持ち上げへ戻す。
規約：図式の始域は任意、圏の充填性は要求しない。
使われ方：相対極限を可逆 path の射影に沿って移送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：自明 Kan fibration による slice の後合成も自明 Kan fibration。
方針：図式と境界の join の単射を持ち上げ、固定図式の条件を右端から回収する。
規約：固定図式 p の始域 K に制限を置かない。
使われ方：相対極限の比較の充満忠実性と頂点上の全射性を供給する。 -/
lemma sliceOverPostcomp_trivialKanFibration {K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [TrivialKanFibration q] :
    TrivialKanFibration (sliceOverPostcomp p q) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  have := TrivialKanFibration.mem (p := q) (joinMap (boundary n).ι (𝟙 K)) inferInstance
  constructor
  intro a b sq
  have hT : CommSq (sliceOverUncurry a) (joinMap (boundary n).ι (𝟙 K))
      q (sliceOverUncurry b) := by
    constructor
    have he := congrArg sliceOverUncurry sq.w
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp] at he
    exact he
  have hfixed : joinInr (Δ[n] : SSet.{u}) K ≫ hT.lift = p := by
    have he := congrArg (fun z ↦ joinInr (boundary n : SSet.{u}) K ≫ z) hT.fac_left
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at he
    exact he.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' {
    l := sliceOverCurry hT.lift hfixed
    fac_left := ?_
    fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hT.fac_left
  · apply sliceOverUncurry_injective (p ≫ q)
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry]
    exact hT.fac_right

end SerrePositivity.InfinityCategories.F1B
