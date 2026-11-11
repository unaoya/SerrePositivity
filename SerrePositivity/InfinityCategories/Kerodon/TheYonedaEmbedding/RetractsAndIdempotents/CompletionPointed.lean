module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits

/-!
概要：元の任意の冪等完備化の関手は、元の指定始対象と零対象を保存する。
方針：全写像空間の retract による終対象保存を反転し、同じ頂点で両条件を合わせる。
規約：元の像そのものを零対象と判定する。安定性はまだ仮定も結論もしない。
使われ方：HA 1.1.3.7 の元の冪等完備化の pointed 性。

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

/-- 元の任意の冪等完備化は、同じ元の始対象の像を始対象へ送る。 -/
lemma IsIdempotentCompletion.map_isInitialVertex {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (f : K ⟶ C) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    {z : K _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (f.app (Opposite.op ⦋0⦌) z) := by
  have hzop := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op z).mp hz
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.map_isTerminalVertex (SSet.opFunctor.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op_general f hf) hzop
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op (f.app (Opposite.op ⦋0⦌) z)).mpr
  simpa only [SSet.opFunctor_map, Equiv.apply_symm_apply] using h

/-- 元の任意の冪等完備化は、同じ元の零対象の像を零対象へ送る。 -/
lemma IsIdempotentCompletion.map_isZeroVertex {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (f : K ⟶ C) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    {z : K _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (f.app (Opposite.op ⦋0⦌) z) :=
  ⟨IsIdempotentCompletion.map_isInitialVertex f hf hz.1,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.map_isTerminalVertex f hf hz.2⟩

/-- 元の任意の冪等完備化は、零対象の存在を保存する。 -/
lemma IsIdempotentCompletion.hasZeroVertex {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (f : K ⟶ C) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex K] : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C := by
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex.exists_zero (X := K)
  exact ⟨f.app (Opposite.op ⦋0⦌) z, IsIdempotentCompletion.map_isZeroVertex f hf hz⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
