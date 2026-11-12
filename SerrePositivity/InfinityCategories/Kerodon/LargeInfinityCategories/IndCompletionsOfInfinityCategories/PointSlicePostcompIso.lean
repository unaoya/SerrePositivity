module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaEvaluationSliceSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-!
概要：指定終点で正規化した slice 後合成は、同型による後合成なら同型である。
方針：通常の slice 後合成と終点等号による輸送へ分解する。
規約：元の全錐と正規化した終点を保持する。
使われ方：形状同型による diagram comma 制限の厳密な余錐持ち上げ。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C D : SSet.{u}} (f : C ⟶ D) (y : C _⦋0⦌)

/-- 概要：正規化した作用を通常の作用と終点輸送へ分解する。
方針：全錐を uncurry して比較。規約：射の等号。使われ方：同型性の移送。 -/
lemma pointSlicePostcomp_eq_postcomp_transport :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp f y = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm y) f ≫
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv_symm_comp y f)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sliceOverUncurry_endpointTransport (SSet.yonedaEquiv_symm_comp y f)]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y))) f
  simp only [Category.id_comp] at h
  rw [h]
  simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_uncurry f y (𝟙 _)

/-- 概要：同型による正規化した slice 後合成も同型。
方針：分解の両因子の同型性。規約：同じ終点。使われ方：comma 同型。 -/
lemma pointSlicePostcomp_isIso [IsIso f] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp f y) := by
  rw [pointSlicePostcomp_eq_postcomp_transport]
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_isIso (SSet.yonedaEquiv.symm y) f
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
