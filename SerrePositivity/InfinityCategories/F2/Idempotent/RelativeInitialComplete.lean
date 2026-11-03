module

public import SerrePositivity.InfinityCategories.F2.Idempotent.RelativeInitialRetracts
public import SerrePositivity.InfinityCategories.Core.Idempotent.FullSubcomplexSplitting
public import SerrePositivity.InfinityCategories.F2.Idempotent.FunctorComplete
public import SerrePositivity.InfinityCategories.F1.ColimitFullyFaithful

/-!
概要：冪等完備な全体の相対始対象の全部分 ∞ 圏、および全普遍余錐の ∞ 圏は冪等完備。
方針：相対始点境界充填の retract 閉性から、元の全分裂を同じ全部分圏へ戻す。
規約：全図式が余極限を持つとは仮定しない。
使われ方：元の図式の retract への余極限の存在の移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等完備な全体の、同じ inner fibration の全相対始対象は冪等完備。 -/
lemma relativeInitialVertices_isIdempotentComplete {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (hX : IsIdempotentComplete X) : IsIdempotentComplete (relativeInitialVertices p) :=
  fullSubcomplex_isIdempotentComplete (InitialBoundaryLifting p)
    (fun ⟨r⟩ hy ↦ initialBoundaryLifting_of_vertexRetraction p r hy) hX

/-- 冪等完備な元の標的の全普遍余錐の ∞ 圏は、任意の添字で冪等完備。 -/
lemma colimitCocones_isIdempotentComplete (K : SSet.{u}) {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) : IsIdempotentComplete (colimitCocones K X) :=
  relativeInitialVertices_isIdempotentComplete (coconeRestriction K X)
    (functor_isIdempotentComplete (join K Δ[0]) hX)

end SerrePositivity.InfinityCategories.F2.Idempotent
