module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionChoiceEquivalence
public import SerrePositivity.KST.NonConnective.DGKappaRawSuspensionCompletion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionUniqueness

/-!
概要：同じ実懸垂の選択同値を、元の dg Yoneda 完備化と固定 ν 値の比較へ接続する。
方針：元の一方の実商から出る二つの完備化の一意性を使い、包含比較を保持する。
規約：固定 ν を変更しない。strict dg 比較や反復 K 構造辺との自然性は別工程。
使われ方：K-7 d4・e の実商選択比較を、同じ Perf／固定 ν 側へ戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I J : DGKappaConeInput R A κ)
  (P : DGKappaPerfectInput R A I) (Q : DGKappaPerfectInput R A J)

/-- 実商選択同値と標的の元の dg Yoneda の合成も、元の実商の冪等完備化。 -/
theorem dgKappaSuspensionChoiceYoneda_isIdempotentCompletion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion ((dgKappaSuspensionChoiceEquivalence R A I J P Q).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A J))) := by
  let e := dgKappaSuspensionChoiceEquivalence R A I J P Q
  let δ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A J))
  have hδ := dgKappaRawSuspensionYoneda_isIdempotentCompletion R A J
  refine ⟨hδ.1, e.isFullyFaithful.comp hδ.2.1, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hδ.2.2 y
  obtain ⟨a, ⟨ea⟩⟩ := e.isEssentiallySurjective x
  exact ⟨a, hx.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ea δ).symm)⟩

/-- 同じ元の二つの dg Yoneda を保つ、実懸垂の Perf 同値の存在。 -/
theorem dgKappaSuspensionPerfectChoice_exists :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R (dgKappaSuspensionKInput R A I))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R (dgKappaSuspensionKInput R A J)),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A I)) ≫ e.hom)
        ((dgKappaSuspensionChoiceEquivalence R A I J P Q).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (dgKappaSuspensionKInput R A J)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.equivalence_unique _
    (dgKappaRawSuspensionYoneda_isIdempotentCompletion R A I) _
    (dgKappaSuspensionChoiceYoneda_isIdempotentCompletion R A I J P Q)

/-- 元の dg Yoneda への指定比較を伴う、同じ二つの Perf 値の実同値。 -/
def dgKappaSuspensionPerfectChoiceEquivalence :=
  (dgKappaSuspensionPerfectChoice_exists R A I J P Q).choose

def dgKappaSuspensionPerfectChoiceEquivalence_yonedaIso :=
  (dgKappaSuspensionPerfectChoice_exists R A I J P Q).choose_spec.some

/-- 元のラベル評価同値を通る、同じ固定 ν 値どうしの実同値。 -/
def dgKappaSuspensionNuChoiceEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKInputStableValue R (dgKappaSuspensionKInput R A I)).obj
      (dgKInputStableValue R (dgKappaSuspensionKInput R A J)).obj :=
  (presentedPerfectDGQCatEvaluationEquivalence R (dgKappaSuspensionKInput R A I)).trans
    ((dgKappaSuspensionPerfectChoiceEquivalence R A I J P Q).trans
      (presentedPerfectDGQCatEvaluationEquivalence R (dgKappaSuspensionKInput R A J)).symm)

end SerrePositivity.KST.NonConnective
