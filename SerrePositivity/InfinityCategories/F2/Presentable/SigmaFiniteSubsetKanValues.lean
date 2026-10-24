module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFiniteRepresentableCoproduct
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSmallRepresentableKan
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteSubsetElements
public import SerrePositivity.InfinityCategories.F2.Presentable.ElementsCoproductKanProjection

/-!
概要：有限部分集合の次数射影に沿う左 Kan 延長の各値は表現可能。
方針：各局所余極限を有限離散ファイバーへ制限する。
規約：指定された coherent な延長関手と各値を保持する。
使われ方：P_Σ の小余積が Ind に属することの有限段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：有限部分集合上の同じ左 Kan 関手の各値は表現可能と同型。
方針：元の局所余錐を離散ファイバーへ制限し、有限余積の表現可能性を使う。
規約：各有限部分集合の値を同じ関手の頂点のまま扱う。
使われ方：filtered 余極限の全段の Ind 条件。 -/
lemma sigmaFiniteSubsetKan_value_representable
    {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {I : Type u} (p : nerve (Discrete I) ⟶ C)
    {G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Finset I)) ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I) ≫ p) ≫
        sigmaYonedaInfinityMap C)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (Functor.Elements.π (finiteSubsetFamily I))) ≫ G))
    (hβ : IsLeftKanExtension
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π (finiteSubsetFamily I))))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I) ≫ p) ≫
        sigmaYonedaInfinityMap C) G β)
    (s : Finset I) : ∃ x : C _⦋0⦌,
      Nonempty (VertexIso (G.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex s)))
        ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x))) := by
  let Y := finiteSubsetFamily I
  let f := elementsDegreeFiber Y s ⋙ CostructuredArrow.proj _ s
  let p' := nerveMap (f ⋙ finiteSubsetForget I) ≫ p
  have : Finite (Y.obj s) := by
    change Finite {i // i ∈ s}
    infer_instance
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (ULift.up (nerveVertex s))
  have hr := (Ind.isColimitCone_iff_restrict_rightCofinal
    (elementsCoproductKanComparison Y s) (elementsCoproductKanComparison_isRightCofinal Y s)
    c).mp hc
  have he : elementsCoproductKanComparison Y s ≫
      leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y)))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I) ≫ p) ≫
          sigmaYonedaInfinityMap C) (ULift.up (nerveVertex s)) =
      (SSet.uliftFunctor.{u + 1, u}).map p' ≫ sigmaYonedaInfinityMap C := by
    rw [leftKanDiagram, ← Category.assoc, elementsCoproductKanComparison_projection]
    rw [← Category.assoc, ← Functor.map_comp]
    rfl
  let d := c.restrict (elementsCoproductKanComparison Y s)
  let d' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p' ≫ sigmaYonedaInfinityMap C) :=
    ⟨d.val, d.property.trans he⟩
  have hd' : IsColimitCone d' := (F2.isColimitCone_iff_of_cocone_val_eq d d' rfl).mp hr
  obtain ⟨x, ⟨e⟩⟩ := sigmaYoneda_finiteCoproduct_representable hC p' d' hd'
  have hv' : d'.vertex = G.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex s)) := hv
  exact ⟨x, ⟨(eqToIso (congrArg HomotopyCategory.mk hv')).symm ≪≫ e⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
