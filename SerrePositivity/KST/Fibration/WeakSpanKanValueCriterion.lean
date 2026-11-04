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
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 全自然変換の指定成分の同値性は、既存の同じ分数写像空間比較の同値性と同値。 -/
theorem weakSpanKanMappingComparison_value_equivalence_iff :
    IsQCatEquivalence
      (X := ((weakSpanKanDiagram i x).obj c).obj)
      (Y := ((fractionSimplexKanMappingDiagram q.hom x).obj c).obj)
      ((weakSpanKanMappingComparison h x).app c) ↔
      IsQCatEquivalence (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) := by
  let hq : InvertsEdges q.hom (weakEquivalences i) := h.inverts
  let y := (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)
  let f := fixedFractionCosliceEvaluation q.hom (weakEquivalences i) hq x y
  have hs := weakSpanKanValueComparison_isQCatEquivalence i x c
  have ht := fractionSimplexKanValueComparison_isQCatEquivalence (q := q) x c
  have he := congrArg (fun m => IsQCatEquivalence m)
    (weakSpanKanMappingComparison_value h x c)
  have hR := strictKanCompletion_map_equivalence_iff_evaluation f
  have hG := fixedFractionCosliceGroupoidComparison_isQCatEquivalence_iff
    q.hom (weakEquivalences i) hq x y
  constructor
  · intro ha
    have hc := hs.cancel_left (he.mp (ha.comp ht))
    exact hG.mp (hR.mp hc)
  · intro ha
    have hc := hs.comp (hR.mpr (hG.mpr ha))
    exact ht.cancel_right (he.mpr hc)

end SerrePositivity.KST.Fibration
