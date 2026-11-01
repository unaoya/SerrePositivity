module
public import SerrePositivity.InfinityCategories.Stable.Roof.SliceEvaluationPinched
public import SerrePositivity.InfinityCategories.F1B.Roof.RoofTargetFunctor

/-!
概要：実 slice の普遍評価は、固定点の輸送を含む同じ後合成に厳密に自然。
方針：全パラメータの実比較を保持し、終対象性と厳密な fiber の比較を使う。
規約：安定性や有限極限を先取りしない。使われ方：一般安定性判定の実錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 固定点輸送を含む slice の後合成は、元の join の実射の後合成。 -/
lemma roofTargetSliceMap_uncurry {A E B : SSet.{u}} (p : E ⟶ B) (t : E _⦋0⦌)
    (a : A ⟶ sliceOver (SSet.yonedaEquiv.symm t)) :
    sliceOverUncurry (a ≫ roofTargetSliceMap p t) = sliceOverUncurry a ≫ p := by
  let F := sliceOverUncurry a ≫ p
  have hF : joinInr A Δ[0] ≫ F =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t) := by
    dsimp [F]
    rw [← Category.assoc, sliceOverUncurry_fixed]
    exact roofTargetPoint p t
  have hh : sliceOverCurry F hF = a ≫ roofTargetSliceMap p t := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rw [show ((a ≫ roofTargetSliceMap p t).app n s).val =
      (a.app n s).val ≫ p from roofTargetSliceMap_val p t _]
    change joinMap (SSet.yonedaEquiv.symm s) (𝟙 Δ[0]) ≫ (sliceOverUncurry a ≫ p) = _
    rw [← Category.assoc, ← sliceOverUncurry_precomp,
      SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda]
  have h := congrArg sliceOverUncurry hh
  rw [sliceOverUncurry_curry] at h
  exact h.symm

/-- 実 slice 評価の全パラメータの円柱は、同じ後合成に厳密に自然。 -/
lemma roofSliceEvaluationHomotopy_postcomp_h {A E B : SSet.{u}} (p : E ⟶ B)
    (t : E _⦋0⦌) (a : A ⟶ sliceOver (SSet.yonedaEquiv.symm t)) :
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy t) a).h ≫ p =
      (functorHomotopyPrecomp
        (roofSliceEvaluationHomotopy (p.app (Opposite.op ⦋0⦌) t))
          (a ≫ roofTargetSliceMap p t)).h := by
  rw [roofSliceEvaluationHomotopy_precomp_h, roofSliceEvaluationHomotopy_precomp_h,
    roofTargetSliceMap_uncurry, Category.assoc, Category.assoc]
end SerrePositivity.InfinityCategories
