module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaFiniteRepresentableCoproduct
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSmallRepresentableKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteSubsetElements
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductKanProjection

/-!
概要：有限部分集合の次数射影に沿う左 Kan 延長の各値は表現可能。
方針：各局所余極限を有限離散ファイバーへ制限する。
規約：指定された coherent な延長関手と各値を保持する。
使われ方：P_Σ の小余積が Ind に属することの有限段。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：有限部分集合上の同じ左 Kan 関手の各値は表現可能と同型。
方針：元の局所余錐を離散ファイバーへ制限し、有限余積の表現可能性を使う。
規約：各有限部分集合の値を同じ関手の頂点のまま扱う。
使われ方：filtered 余極限の全段の Ind 条件。 -/
lemma sigmaFiniteSubsetKan_value_representable
    {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {I : Type u} (p : nerve (Discrete I) ⟶ C)
    {G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Finset I)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C}
    (β : SSet.Homotopy
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I) ≫ p) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (Functor.Elements.π (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetFamily I))) ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetFamily I))))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I) ≫ p) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) G β)
    (s : Finset I) : ∃ x : C _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (G.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x))) := by
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetFamily I
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y s ⋙ CostructuredArrow.proj _ s
  let p' := nerveMap (f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I) ≫ p
  have : Finite (Y.obj s) := by
    change Finite {i // i ∈ s}
    infer_instance
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s))
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Y s) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison_isRightCofinal Y s)
    c).mp hc
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Y s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y)))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSubsetForget I) ≫ p) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) =
      (SSet.uliftFunctor.{u + 1, u}).map p' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison_projection]
    rw [← Category.assoc, ← Functor.map_comp]
    rfl
  let d := c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Y s)
  let d' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) :=
    ⟨d.val, d.property.trans he⟩
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d' := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq d d' rfl).mp hr
  obtain ⟨x, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYoneda_finiteCoproduct_representable hC p' d' hd'
  have hv' : d'.vertex = G.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) := hv
  exact ⟨x, ⟨(eqToIso (congrArg HomotopyCategory.mk hv')).symm ≪≫ e⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
