module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RelativeInitialRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FullSubcomplexSplitting
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FunctorComplete
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitFullyFaithful

/-!
概要：冪等完備な全体の相対始対象の全部分 ∞ 圏、および全普遍余錐の ∞ 圏は冪等完備。
方針：相対始点境界充填の retract 閉性から、元の全分裂を同じ全部分圏へ戻す。
規約：全図式が余極限を持つとは仮定しない。
使われ方：元の図式の retract への余極限の存在の移送。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の冪等完備な全体の、同じ inner fibration の全相対始対象は冪等完備。 -/
lemma relativeInitialVertices_isIdempotentComplete {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.fullSubcomplex_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p)
    (fun ⟨r⟩ hy ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.initialBoundaryLifting_of_vertexRetraction p r hy) hX

/-- 冪等完備な元の標的の全普遍余錐の ∞ 圏は、任意の添字で冪等完備。 -/
lemma colimitCocones_isIdempotentComplete (K : SSet.{u}) {X : SSet.{u}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X) :=
  relativeInitialVertices_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.functor_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) hX)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
