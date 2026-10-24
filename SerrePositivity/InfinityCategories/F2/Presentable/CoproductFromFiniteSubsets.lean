module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteSubsetElements
public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsCoproductKanProjection
public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitFromLocalLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedColimitPreservation

/-!
概要：有限部分図式の余積と filtered 余極限から指定小余積を構成する。
方針：有限部分集合の要素圏上で局所左 Kan 余極限を取り、離散添字へ戻す。
規約：標的の任意の有限余積を仮定せず、指定図式の有限制限だけを要求する。
使われ方：P_Σ における表現可能対象の小余積。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定離散図式の有限制限と小 sifted 余極限から同じ小余積が存在する。
方針：有限部分集合の filtered 添字上で同じ有限余積を coherent に組み立てる。
規約：空添字を含み、元の離散図式を保持する。
使われ方：有限余積を保つ Yoneda 像の小余積の構成。 -/
lemma hasColimit_discrete_of_finiteRestrictions
    {X : SSet.{u + 1}} [Quasicategory X]
    (hX : HomotopyLimits.HasSmallSiftedColimits X)
    {I : Type u} (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X)
    (hfinite : ∀ (J : Type u) [Finite J] (f : nerve (Discrete J) ⟶ nerve (Discrete I)),
      HasColimit ((SSet.uliftFunctor.{u + 1, u}).map f ≫ F)) : HasColimit F := by
  let Y := finiteSubsetFamily I
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I))
  apply hasColimit_of_rightCofinalRestriction q
    (Ind.isRightCofinal_ulift _ (finiteSubsetForget_nerve_isRightCofinal I))
  apply hasColimit_of_localLeftKan_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) (q ≫ F)
  · apply elements_leftKanDiagram_hasColimit_of_fibers Y
    intro s
    have : Finite (Y.obj s) := by
      change Finite {i // i ∈ s}
      infer_instance
    have hh := hfinite (Y.obj s) (nerveMap
      ((elementsDegreeFiber Y s ⋙ CostructuredArrow.proj _ s) ⋙ finiteSubsetForget I))
    change HasColimit ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (elementsDegreeFiber Y s ⋙ CostructuredArrow.proj _ s) ≫
        nerveMap (finiteSubsetForget I)) ≫ F) at hh
    simpa only [q, Functor.map_comp, Category.assoc] using hh
  · exact hX (nerve (Finset I))

end SerrePositivity.InfinityCategories.F2.Presentable
