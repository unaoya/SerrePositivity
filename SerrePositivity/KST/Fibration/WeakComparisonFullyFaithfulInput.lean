module
public import SerrePositivity.KST.Fibration.FullyFaithfulPrecomposition
public import SerrePositivity.KST.Fibration.WeakComparisonComponentSurjectivity
public import SerrePositivity.KST.Fibration.WeakQuotientComparisonCriterion

/-! # Sp 正本の充満忠実性入力を、元の K-6 比較の可逆性へ接続する

既存の比較同型と Kan 置換の比較だけを合成する。
一般分数比較の充満忠実性を新たに証明するものではない。
-/

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
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 正本の同じ比較の充満忠実性を、指定した実 strict Kan 成分へ移す。 -/
theorem weakSpanKanMappingComparison_value_isFullyFaithful_of_fraction
    (c : TransportSimplexCategory B.obj)
    (hf : IsFullyFaithful (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))) :
    IsFullyFaithful
      (X := ((weakSpanKanDiagram i x).obj c).obj)
      (Y := ((fractionSimplexKanMappingDiagram q.hom x).obj c).obj)
      ((weakSpanKanMappingComparison h x).app c) := by
  let y := (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)
  let f := fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x y
  have hc := cosliceFiberToIntervalMappingSpace_isQCatEquivalence
    (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y)
  have eG := fixedFractionCosliceGroupoidComparisonIso q.hom (weakEquivalences i) h.inverts x y
  have hG : IsFullyFaithful (groupoidCompletionEvaluation f) := hc.isFullyFaithful.cancel_right
    (eG.isFullyFaithful_iff.mpr hf)
  have hR : IsFullyFaithful (strictKanCompletion.map f) :=
    fullyFaithful_of_precomp_equivalence (groupoidCompletionKanComparison_isQCatEquivalence _)
      ((strictKanEvaluationComparisonIso f).isFullyFaithful_iff.mpr
        (hG.comp (strictKanCompletionUnit_isQCatEquivalence _).isFullyFaithful))
  have he := congrArg (fun m => IsFullyFaithful m) (weakSpanKanMappingComparison_value h x c)
  have ht := (fractionSimplexKanValueComparison_isQCatEquivalence (q := q) x c).isFullyFaithful
  exact ht.cancel_right (he.mpr
    ((weakSpanKanValueComparison_isQCatEquivalence i x c).isFullyFaithful.comp hR))

/-- 正本が全終点で充満忠実性を供給すれば、元の K-6 商上の比較自体が可逆となる。
本質的全射性は既存の実右逆から証明済みであり、追加入力しない。 -/
theorem weakQuotientMappingComparison_isIso_of_fraction_fullyFaithful
    (hf : ∀ y : B.obj _⦋0⦌,
      IsFullyFaithful (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)) :
    IsIso (weakQuotientMappingComparison h x) := by
  apply weakQuotientMappingComparison_isIso_of_fractionComparison h x
  intro y
  let c := transportSimplexIndex (n := ⦋0⦌) y
  have hc := isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
    ((weakSpanKanMappingComparison h x).app c)
    (weakSpanKanMappingComparison_value_isFullyFaithful_of_fraction h x c (hf _))
    (weakSpanKanMappingComparison_value_isEssentiallySurjective h x c)
  have he := (weakSpanKanMappingComparison_value_equivalence_iff h x c).mp hc
  have hy := congrArg (fun z : B.obj _⦋0⦌ =>
    IsQCatEquivalence (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x z))
    (transportSimplexFirstVertexMap_zeroIndex y)
  exact hy.mp he

end SerrePositivity.KST.Fibration
