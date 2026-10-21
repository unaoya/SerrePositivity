module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteEvaluationProjectionHomotopies
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeDiscreteLegHomotopy
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-!
概要：元の反復積関手と全射影の native 全錐は、関手圏の実際の極限錐。
方針：元の全評価脚のホモトピーから評価錐の極限性を回収し、点ごとの判定を使う。
規約：元の全錐・頂点・全脚を変更しない。底の quasicategory 性は不要。
使われ方：P_Σ の sifted 閉性で元の評価極限錐の族と比較する積関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}}
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))

/-- 元の同じ評価全錐は、元の Kan 値族の有限積錐。 -/
lemma finiteFunctorEvaluationCone_isLimit
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    IsLimitCone (finiteFunctorEvaluationCone n F b) :=
  finiteSpaceCone_isLimit_of_projection_homotopies n (finiteFunctorKanValues n F b)
    (finiteFunctorEvaluationCone n F b) (finiteFunctorEvaluationCone_vertex n F b)
    (finiteFunctorEvaluationKanLeg_projection_homotopy n F b)

/-- 元の反復積関手の全錐は、元の全評価で極限錐になる。 -/
lemma finiteCoherentFunctorCone_isPointwiseLimit :
    IsPointwiseLimitCone (finiteCoherentFunctorCone n F) := by
  intro b
  exact (finiteFunctorEvaluationCone_isLimit n F b).cast
    (finiteCoherentFunctorEvaluationDiagram_eq n F b).symm

/-- 元の反復積関手と全射影の native 全錐は、元の関手 ∞ 圏の有限積錐。 -/
lemma finiteCoherentFunctorCone_isLimit : IsLimitCone (finiteCoherentFunctorCone n F) :=
  isLimitCone_of_pointwise _ (finiteCoherentFunctorCone_isPointwiseLimit n F)

end SerrePositivity.InfinityCategories.HomotopyLimits
