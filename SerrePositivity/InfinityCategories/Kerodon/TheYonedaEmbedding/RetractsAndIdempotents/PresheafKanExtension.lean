module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PresheafLocalKanColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftStrictExistence

/-!
概要：持ち上げた元の全部分圏包含に沿って、任意の元の前層図式を厳密に延長する。
方針：元の全局所余極限の存在と、持ち上げた元の包含の性質を厳密な左 Kan 存在へ渡す。
規約：元の図式を制限の等式で回収する。前層圏の大きい余極限を入力に仮定しない。
使われ方：HTT 5.1.4.8 の元の Yoneda 後合成の延長。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 持ち上げた元の全部分圏包含に沿って、前層図式を厳密に回収する左 Kan 関手が存在。 -/
lemma exists_presheafKan_strict_extension {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) [Mono δ] [InnerFibration δ]
    (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity E) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity E,
      (SSet.uliftFunctor.{u + 1, u}).map δ ≫ G = F₀ ∧
      ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone ((SSet.uliftFunctor.{u + 1, u}).map δ) G c) := by
  have : Mono ((SSet.uliftFunctor.{u + 1, u}).map δ) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemUliftMap_mono δ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftCanonical_strict_extension_of_local_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsFullyFaithful.ulift hδ) F₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.presheafLocalKanDiagram_hasColimit δ F₀)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
