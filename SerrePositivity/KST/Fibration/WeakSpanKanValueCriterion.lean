module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanFiberComparison
public import SerrePositivity.InfinityCategories.Derived.KanModels.StrictKanEvaluationComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FixedFractionCosliceGroupoid

/-! # 同じ strict Kan 比較の値での同値性を、元の分数比較そのもので判定する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 全自然変換の指定成分の同値性は、既存の同じ分数写像空間比較の同値性と同値。 -/
theorem weakSpanKanMappingComparison_value_equivalence_iff :
    IsQCatEquivalence
      (X := ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x).obj c).obj)
      (Y := ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj c).obj)
      ((weakSpanKanMappingComparison h x).app c) ↔
      IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) := by
  let hq : InvertsEdges q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) := h.inverts
  let y := (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)
  let f := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x y
  have hs := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison_isQCatEquivalence i x c
  have ht := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison_isQCatEquivalence (q := q) x c
  have he := congrArg (fun m => IsQCatEquivalence m)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanMappingComparison_value h x c)
  have hR := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanCompletion_map_equivalence_iff_evaluation f
  have hG := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison_isQCatEquivalence_iff
    q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x y
  constructor
  · intro ha
    have hc := hs.cancel_left (he.mp (ha.comp ht))
    exact hG.mp (hR.mp hc)
  · intro ha
    have hc := hs.comp (hR.mpr (hG.mpr ha))
    exact ht.cancel_right (he.mpr hc)

end SerrePositivity.KST.Fibration
