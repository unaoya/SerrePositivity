module

public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingLimitExistence
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

/-!
概要：冪等完備な ∞ 圏を標的とする全関手 ∞ 圏は冪等完備。
方針：元の全 coherent 冪等図式の点ごとの極限を自然な全極限へまとめ、強く分裂する。
規約：添字 K は任意。分裂の自然性を未証明の入力として要求しない。
使われ方：辺・普遍四角形の関手 ∞ 圏内での coherent 分裂。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 冪等完備な元の標的への全関手 ∞ 圏は、任意の添字で冪等完備。 -/
lemma functor_isIdempotentComplete (K : SSet.{u}) {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) : IsIdempotentComplete ((ihom K).obj X) := by
  intro d
  apply strongSplitting_exists_of_hasLimit d
  exact hasLimit_of_hasPointwiseLimits d
    (fun k ↦ hX.hasLimit (evaluateFunctorDiagram d k))

end SerrePositivity.InfinityCategories.F2.Idempotent
