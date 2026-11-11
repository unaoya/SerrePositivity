module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteWeightedSectionsContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallBousfieldKanContinuity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FinitePosetNerve

/-!
概要：有限 poset の元の Bousfield–Kan 模型は filtered 余極限を保つ。
方針：各 Over の nerve を元の有限 poset の nerve に単射で埋め、有限重みを得る。
規約：元の end と標準比較射を保持し、濃度変更境界を仮定しない。
使われ方：I-2 d′ の WithInitial 全錐の有限版交換。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories


/-- 有限 poset の Bousfield–Kan 重みの各 nerve は有限単体集合。 -/
lemma bousfieldKanWeight_finite_poset (I : Type u) [PartialOrder I] [Finite I] (i : I) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i).Finite := by
  have : Quiver.IsThin (Over i) := fun _ _ ↦
    ⟨fun _ _ ↦ Over.OverMorphism.ext (Subsingleton.elim _ _)⟩
  have : Mono (nerveMap (Over.forget i)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro a b h
    refine ComposableArrows.ext (fun k ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
    exact CostructuredArrow.obj_ext _ _ (congrArg (fun s ↦ s.obj k) h) (by subsingleton)
  exact SSet.finite_of_mono (nerveMap (Over.forget i))

/-- 同じ有限 poset の元の Bousfield–Kan 極限模型は通常 filtered 余極限を保つ。 -/
lemma bousfieldKanHolimFunctor_finite_poset_preservesFilteredColimits
    (I : Type u) [PartialOrder I] [Finite I]
    (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I) := by
  have hI : HasCardinalLT (Arrow I) Cardinal.aleph0.{u} :=
    (hasCardinalLT_arrow_iff_of_isThin I Cardinal.aleph0.{u} le_rfl).mpr
      (hasCardinalLT_of_finite I Cardinal.aleph0.{u} le_rfl)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteWeightedSections_preservesFilteredColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (bousfieldKanWeight_finite_poset I) hI J

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
