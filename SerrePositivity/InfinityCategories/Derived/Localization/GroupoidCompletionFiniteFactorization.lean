module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.KanModels.GroupoidCompletionKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanFiniteFactorization

/-!
概要：元の亜群化への任意の有限全族を、元の有限部分複体の亜群化へ下ろす。
方針：同じ実単位の自然性から Kan 比較の全同型を証明し、連続模型の有限台を移送する。
規約：元の完成射は全 FunctorIso で保持し、生の同形状図式への厳密持ち上げは主張しない。
使われ方：c5 の任意の完成側有限境界・全比較円柱を、有限な元の実図式へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
open SerrePositivity.InfinityCategories.F2
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Localization
open SerrePositivity.KST.LocalizingInvariants

/-- 同じ元の全辺局所化の実写像と Kan 比較は、同じ単位自然性による全同型で可換。 -/
def groupoidCompletionKanComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    FunctorIso (groupoidCompletionMapOf f ≫ groupoidCompletionKanComparison Y)
      (groupoidCompletionKanComparison X ≫ F2.continuousKanReplacement.map f) := by
  change FunctorIso
    (groupoidCompletionMapOf f ≫
      groupoidCompletionEvaluation (F2.continuousKanReplacementUnit.app Y))
    (groupoidCompletionEvaluation (F2.continuousKanReplacementUnit.app X) ≫
      F2.continuousKanReplacement.map f)
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  have e := FunctorIso.postcomp (groupoidCompletionMapOfIso f)
      (groupoidCompletionEvaluation (F2.continuousKanReplacementUnit.app Y)) ≪≫
    FunctorIso.precomp
      (groupoidCompletionEvaluationIso (F2.continuousKanReplacementUnit.app Y)) f
  have h : FunctorIso
      (groupoidCompletionMap X ≫
        (groupoidCompletionMapOf f ≫
          groupoidCompletionEvaluation (F2.continuousKanReplacementUnit.app Y)))
      (F2.continuousKanReplacementUnit.app X ≫ F2.continuousKanReplacement.map f) := by
    rw [← F2.continuousKanReplacementUnit.naturality f]
    simpa only [Category.assoc, CategoryTheory.Functor.id_map, _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion] using e
  have t := FunctorIso.postcomp
    (groupoidCompletionEvaluationIso (F2.continuousKanReplacementUnit.app X))
    (F2.continuousKanReplacement.map f)
  exact h ≪≫ (by
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.KanModels.groupoidCompletionKanComparison, _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion,
      CategoryTheory.Functor.id_obj] using t.symm)

/-- 元の亜群化への任意の有限全族は、一つの有限実部分複体の元の亜群化を経由する。 -/
lemma groupoidCompletion_finite_factorization {K X : SSet.{u}} [K.Finite]
    (f : K ⟶ groupoidCompletion X) :
    ∃ A : FiniteSubcomplex X, ∃ a : K ⟶ groupoidCompletion A.val,
      Nonempty (FunctorIso (a ≫ groupoidCompletionMapOf A.val.ι) f) := by
  obtain ⟨A, g, hg⟩ := F2.continuousKanReplacement_finite_factorization
    (f ≫ groupoidCompletionKanComparison X)
  let V := (groupoidCompletionKanComparison_isQCatEquivalence (A.val : SSet.{u})).choose
  let a := g ≫ V.inv
  have en := FunctorIso.precomp (groupoidCompletionKanComparison_naturality A.val.ι) a
  have ev := FunctorIso.postcomp (FunctorIso.precomp V.invHomIso g)
    (F2.continuousKanReplacement.map A.val.ι)
  have he : FunctorIso ((a ≫ groupoidCompletionMapOf A.val.ι) ≫
      groupoidCompletionKanComparison X) (f ≫ groupoidCompletionKanComparison X) := by
    have h := en ≪≫ (by
      simpa only [a, V, IsQCatEquivalence.choose, Category.assoc] using ev)
    simpa only [Category.assoc, Category.comp_id, Category.id_comp, hg, _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion]
      using h
  have hff := ((groupoidCompletionKanComparison_isQCatEquivalence X).postcompose K).isFullyFaithful
  exact ⟨A, a, ⟨hff.preimageVertexIso he⟩⟩

end SerrePositivity.InfinityCategories.Derived.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionKanComparison_naturality (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionKanComparison_naturality := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionKanComparison_naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletion_finite_factorization := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_finite_factorization

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionKanComparison_naturality._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionKanComparison_naturality._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionKanComparison_naturality._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionKanComparison_naturality._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionKanComparison_naturality._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionKanComparison_naturality._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionKanComparison_naturality._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionKanComparison_naturality._proof_4
