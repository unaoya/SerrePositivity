module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionExtensionImage

/-!
概要：元の冪等完備化への制限は、冪等完備な標的への全関手 ∞ 圏の同値。
方針：証明済みの全写像空間の充満忠実性と、構成済みの延長による本質的全射性を合わせる。
規約：元の制限そのものを同値と判定し、元の Yoneda 因子化にもそのまま適用する。
使われ方：HTT 5.1.4.9、冪等完備化の普遍性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の冪等完備化への制限は、冪等完備な標的への全関手空間で本質的全射。 -/
lemma IsIdempotentCompletion.pre_isEssentiallySurjective {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δ) (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((pre δ).app E) := by
  intro x
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K E).surjective x
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.exists_extension δ hδ hE F
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H, hH⟩

/-- 元の任意の冪等完備化への制限そのものは、冪等完備な標的への全関手 ∞ 圏の同値。 -/
lemma IsIdempotentCompletion.pre_isQCatEquivalence {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δ) (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre δ).app E) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective ((pre δ).app E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful_general δ hδ)
    (IsIdempotentCompletion.pre_isEssentiallySurjective δ hδ hE)

/-- 元の制限を順方向として保持する冪等完備化の全関手圏の普遍同値。 -/
def idempotentCompletionUniversalEquivalence {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δ) (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom C).obj E) ((ihom K).obj E) :=
  (IsIdempotentCompletion.pre_isQCatEquivalence δ hδ hE).choose

/-- 元の全 Yoneda 因子化に沿う制限は、冪等完備な標的への全関手 ∞ 圏の同値。 -/
lemma idemYoneda_pre_isQCatEquivalence (C : SSet.{u}) [Quasicategory C]
    (E : SSet.{u + 1}) [Quasicategory E] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C)).app E) :=
  IsIdempotentCompletion.pre_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion C) hE

/-- 元の全 Yoneda 因子化への制限を順方向とする、全関手 ∞ 圏の普遍同値。 -/
def idemYonedaUniversalEquivalence (C : SSet.{u}) [Quasicategory C]
    (E : SSet.{u + 1}) [Quasicategory E] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C)).obj E)
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj E) :=
  (idemYoneda_pre_isQCatEquivalence C E hE).choose

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Lemma 2.20" (partial := component) "仮定：小準圏と冪等完備な標的（Lean は安定性を使わない）。結論：完備化への制限による関手圏の同値と、各対象での Idem(C) ≃ Indκ(C)^κ（原典の反射性の各圏での成分と κ=ω の式。Cat^ex 上の大域随伴は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYonedaUniversalEquivalence
attribute [cite BGT "Lemma 2.20" (partial := component) "仮定：小準圏と冪等完備な標的（Lean は安定性を使わない）。結論：完備化への制限による関手圏の同値と、各対象での Idem(C) ≃ Indκ(C)^κ（原典の反射性の各圏での成分と κ=ω の式。Cat^ex 上の大域随伴は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idempotentCompletionUniversalEquivalence
attribute [cite HTT "5.1.4.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isQCatEquivalence
attribute [cite HTT "5.3.6.9" (partial := special) "仮定：小準圏 C と冪等完備な準圏 E（Lean が強い：任意の大きさの C に対する別宇宙の構成はこの宣言で述べない）。結論：Idem(C) は同じ Yoneda の冪等完備化で、制限 Fun(Idem(C),E)→Fun(C,E) が全準圏同値（この場合の自由冪等完備化の普遍性と一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_pre_isQCatEquivalence
