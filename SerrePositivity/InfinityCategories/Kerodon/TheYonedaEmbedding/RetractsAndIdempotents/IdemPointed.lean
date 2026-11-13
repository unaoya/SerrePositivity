module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionPointed
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessUniverse

/-!
概要：元の Idem(C) は、元の C の零対象をそのまま Yoneda 像の零対象として持つ。
方針：元の零頂点を宇宙持ち上げし、元の冪等完備化の零対象保存を適用する。
規約：同じ元の頂点の像を保持する。安定性の残りの条件は別工程。
使われ方：HA 1.1.3.7 の冪等完備化の安定性の零対象条件。

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

/-- 元の C の指定零頂点の同じ Yoneda 像は、元の Idem(C) の零頂点。 -/
lemma idemYoneda_isZeroVertex {C : SSet.{u}} [Quasicategory C]
    {z : C _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := (SSet.uliftFunctor.{u + 1, u}).obj C) (ULift.up z) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isInitialVertex_iff_ulift z).mp hz.1, (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isTerminalVertex_iff_ulift z).mp hz.2⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.map_isZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion C) h₀

/-- 元の C が pointed なら、元の Yoneda retract 閉包 Idem(C) も pointed。 -/
instance idem_hasZeroVertex (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C) := by
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex.exists_zero (X := C)
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C).app (Opposite.op ⦋0⦌) (ULift.up z), idemYoneda_isZeroVertex hz⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
