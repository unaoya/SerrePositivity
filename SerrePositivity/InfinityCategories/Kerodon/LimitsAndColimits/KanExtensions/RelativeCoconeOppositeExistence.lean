module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCoconeOpposite

/-!
概要：反転した標準相対極限錐から像を指定した相対余極限余錐を回収する。
方針：coslice の反転同型の零次成分の全射性と後合成自然性を使う。
規約：像の余錐全体を射の等式で保つ。
使われ方：右 Kan の標準局所存在を反転後の左の存在定理へ渡す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：余錐の反転は反転後の全ての錐を表す。
方針：coslice の反転同型の零次成分の全射性を使う。
規約：標的や添字の充填性は不要。
使われ方：反転後の局所錐から元の余錐を選ぶ。 -/
lemma kanCoconeReverseCone_surjective {A D : SSet.{u}} (p : A ⟶ D) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (p := p)) := by
  intro c
  obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIso_app_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso p) (Opposite.op ⦋0⦌) c
  refine ⟨SSet.opObjEquiv x, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso p).hom.app _ (SSet.opObjEquiv.symm (SSet.opObjEquiv x)) = c
  simpa only [Equiv.symm_apply_apply] using hx

/-- 概要：反転後の像指定の相対極限から元の像指定の相対余極限が存在する。
方針：反転の全射性で余錐を選び、普遍性を反映し、raw な像の等式を忠実性で戻す。
規約：元と像の余錐の全体を固定する。
使われ方：標準底余錐上の相対局所存在の双対化。 -/
lemma exists_kanRelativeColimit_of_op_relative_limit {A D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (p : A ⟶ D) (U : D ⟶ E)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ U)) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.opFunctor.map p))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone (SSet.opFunctor.map U) c)
    (hcb : c.val ≫ SSet.opFunctor.map U = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone b).val) :
    ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U z ∧ z.val ≫ U = b.val := by
  obtain ⟨z, hz⟩ := kanCoconeReverseCone_surjective p c
  refine ⟨z, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_iff_reverseCone U z).2 (hz.symm ▸ hc), ?_⟩
  rw [← hz, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val] at hcb
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  apply SSet.opFunctor.map_injective
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A Δ[0]).inv).1
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 A.op))).1
  simpa only [Functor.map_comp, Category.assoc] using hcb

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
