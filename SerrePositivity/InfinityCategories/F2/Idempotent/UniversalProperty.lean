module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionExtensionImage

/-!
概要：元の冪等完備化への制限は、冪等完備な標的への全関手 ∞ 圏の同値。
方針：証明済みの全写像空間の充満忠実性と、構成済みの延長による本質的全射性を合わせる。
規約：元の制限そのものを同値と判定し、元の Yoneda 因子化にもそのまま適用する。
使われ方：HTT 5.1.4.9、冪等完備化の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等完備化への制限は、冪等完備な標的への全関手空間で本質的全射。 -/
lemma IsIdempotentCompletion.pre_isEssentiallySurjective {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : IsIdempotentCompletion δ) (hE : IsIdempotentComplete E) :
    IsEssentiallySurjective ((pre δ).app E) := by
  intro x
  obtain ⟨F, rfl⟩ := (functorVertexEquiv K E).surjective x
  obtain ⟨H, hH⟩ := IsIdempotentCompletion.exists_extension δ hδ hE F
  exact ⟨functorVertex H, hH⟩

/-- 元の任意の冪等完備化への制限そのものは、冪等完備な標的への全関手 ∞ 圏の同値。 -/
lemma IsIdempotentCompletion.pre_isQCatEquivalence {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : IsIdempotentCompletion δ) (hE : IsIdempotentComplete E) :
    IsQCatEquivalence ((pre δ).app E) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective ((pre δ).app E)
    (IsIdempotentCompletion.pre_isFullyFaithful_general δ hδ)
    (IsIdempotentCompletion.pre_isEssentiallySurjective δ hδ hE)

/-- 元の制限を順方向として保持する冪等完備化の全関手圏の普遍同値。 -/
def idempotentCompletionUniversalEquivalence {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : IsIdempotentCompletion δ) (hE : IsIdempotentComplete E) :
    QCatEquivalence ((ihom C).obj E) ((ihom K).obj E) :=
  (IsIdempotentCompletion.pre_isQCatEquivalence δ hδ hE).choose

/-- 元の全 Yoneda 因子化に沿う制限は、冪等完備な標的への全関手 ∞ 圏の同値。 -/
lemma idemYoneda_pre_isQCatEquivalence (C : SSet.{u}) [Quasicategory C]
    (E : SSet.{u + 1}) [Quasicategory E] (hE : IsIdempotentComplete E) :
    IsQCatEquivalence ((pre (idemYoneda C)).app E) :=
  IsIdempotentCompletion.pre_isQCatEquivalence (idemYoneda C)
    (idemYoneda_isIdempotentCompletion C) hE

/-- 元の全 Yoneda 因子化への制限を順方向とする、全関手 ∞ 圏の普遍同値。 -/
def idemYonedaUniversalEquivalence (C : SSet.{u}) [Quasicategory C]
    (E : SSet.{u + 1}) [Quasicategory E] (hE : IsIdempotentComplete E) :
    QCatEquivalence ((ihom (Idem C)).obj E)
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj E) :=
  (idemYoneda_pre_isQCatEquivalence C E hE).choose

end SerrePositivity.InfinityCategories.F2.Idempotent
