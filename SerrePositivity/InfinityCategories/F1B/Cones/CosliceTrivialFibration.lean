module

public import SerrePositivity.InfinityCategories.Core.ConeAnodyne
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：任意の図式の coslice による自明 Kan fibration の保存。
方針：coslice の境界充填を join の単射に対する持ち上げへ戻す。
規約：図式の始域は任意、圏の充填性は要求しない。
使われ方：相対余極限を可逆 path の射影に沿って移送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：自明 Kan fibration による coslice の後合成も自明 Kan fibration。
方針：図式と境界の join の単射を持ち上げ、固定図式の条件を左端から回収する。
規約：固定図式 p の始域 K に制限を置かない。
使われ方：相対余極限の比較の充満忠実性と頂点上の全射性を供給する。 -/
lemma sliceUnderPostcomp_trivialKanFibration {K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [TrivialKanFibration q] :
    TrivialKanFibration (sliceUnderPostcomp p q) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  have := TrivialKanFibration.mem (p := q) (joinMap (𝟙 K) (boundary n).ι) inferInstance
  constructor
  intro a b sq
  have hT : CommSq (sliceUnderUncurry a) (joinMap (𝟙 K) (boundary n).ι)
      q (sliceUnderUncurry b) := by
    constructor
    have he := congrArg sliceUnderUncurry sq.w
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at he
    exact he
  have hfixed : joinInl K (Δ[n] : SSet.{u}) ≫ hT.lift = p := by
    have he := congrArg (fun z ↦ joinInl K (boundary n : SSet.{u}) ≫ z) hT.fac_left
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at he
    exact he.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' {
    l := sliceUnderCurry hT.lift hfixed
    fac_left := ?_
    fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hT.fac_left
  · apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    exact hT.fac_right

end SerrePositivity.InfinityCategories.F1B
