module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationPinched
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.RoofTargetFunctor

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 固定点輸送を含む slice の後合成は、元の join の実射の後合成。 -/
lemma roofTargetSliceMap_uncurry {A E B : SSet.{u}} (p : E ⟶ B) (t : E _⦋0⦌)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm t)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap p t) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a ≫ p := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a ≫ p
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t) := by
    dsimp [F]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed]
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint p t
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hF = a ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap p t := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rw [show ((a ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap p t).app n s).val =
      (a.app n s).val ≫ p from _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_val p t _]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm s) (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a ≫ p) = _
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp,
      SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry] at h
  exact h.symm

/-- 実 slice 評価の全パラメータの円柱は、同じ後合成に厳密に自然。 -/
lemma roofSliceEvaluationHomotopy_postcomp_h {A E B : SSet.{u}} (p : E ⟶ B)
    (t : E _⦋0⦌) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm t)) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy t) a).h ≫ p =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy (p.app (Opposite.op ⦋0⦌) t))
          (a ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap p t)).h := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy_precomp_h,
    roofTargetSliceMap_uncurry, Category.assoc, Category.assoc]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
