module
public import SerrePositivity.InfinityCategories.Stable.FunctorLoopSquareCriterion
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.SquareConePostcomp
/-!
概要：関手圏の同じ四角形の押し出し性を全評価から回収する。
方針：全押し出し余錐へ点ごとの余極限判定を適用する。
規約：標的の有限余極限を仮定しない。
使われ方：極限錐への比較を cofiber の区間族として扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma isPushoutSquare_functorCategory_of_pointwise {K X : SSet.{u}}
    [Quasicategory X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (hR : ∀ k : K _⦋0⦌, IsPushoutSquare (R ≫ evaluateFunctorAt k)) :
    IsPushoutSquare R := by
  apply F2.isColimitCone_of_pointwise (pushoutCocone R)
  intro k
  exact (F2.isColimitCone_post_pushoutCocone_iff (evaluateFunctorAt k) R).mpr (hR k)

end SerrePositivity.InfinityCategories
