module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSubsetElements
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductKanProjection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ColimitFromLocalLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation

/-!
概要：有限部分図式の余積と filtered 余極限から指定小余積を構成する。
方針：有限部分集合の要素圏上で局所左 Kan 余極限を取り、離散添字へ戻す。
規約：標的の任意の有限余積を仮定せず、指定図式の有限制限だけを要求する。
使われ方：P_Σ における表現可能対象の小余積。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：指定離散図式の有限制限と小 sifted 余極限から同じ小余積が存在する。
方針：有限部分集合の filtered 添字上で同じ有限余積を coherent に組み立てる。
規約：空添字を含み、元の離散図式を保持する。
使われ方：有限余積を保つ Yoneda 像の小余積の構成。 -/
lemma hasColimit_discrete_of_finiteRestrictions
    {X : SSet.{u + 1}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits X)
    {I : Type u} (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (hfinite : ∀ (J : Type u) [Finite J] (f : nerve (Discrete J) ⟶ nerve (Discrete I)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map f ≫ F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetFamily I
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_rightCofinalRestriction q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget_nerve_isRightCofinal I))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_localLeftKan_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) (q ≫ F)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elements_leftKanDiagram_hasColimit_of_fibers Y
    intro s
    have : Finite (Y.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    have hh := hfinite (Y.obj s) (nerveMap
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y s ⋙ CostructuredArrow.proj _ s) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y s ⋙ CostructuredArrow.proj _ s) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I)) ≫ F) at hh
    simpa only [q, Functor.map_comp, Category.assoc] using hh
  · exact hX (nerve (Finset I))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
