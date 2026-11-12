module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionFibers
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent.StabilityUniverse
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessUniverse
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BicartesianCriterion

/-!
概要：安定 ∞ 圏の任意の冪等完備化は安定であり、元の Idem(C) 自身も安定。
方針：指定辺を保つ実際の双普遍 fiber/cofiber を構成し、零角の双方向判定を導く。
規約：HA 1.1.3.7。元の全 coherent 分裂を使用し、標的の安定性を入力に置かない。
使われ方：Cat^perf の冪等完備化と compact 対象との同定の安定性条件。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 安定な元の ∞ 圏の任意の冪等完備化は、元の全普遍四角形の意味で安定。 -/
lemma IsIdempotentCompletion.isStable {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D] (f : C ⟶ D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D := by
  have : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.hasZeroVertex f hf
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_bicartesian_choices
    (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.bicartesian_fiber_exists f hf a)
    (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.bicartesian_cofiber_exists f hf a)

/-- 安定な元の C の元の Yoneda retract 閉包 Idem(C) は、実際の安定 ∞ 圏。 -/
instance idem_isStable (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C) := by
  have : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{u + 1, u}).obj C) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent.isStable_ulift
  exact IsIdempotentCompletion.isStable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion C)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
