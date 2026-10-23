module
public import SerrePositivity.InfinityCategories.Stable.FunctorPullbackSquares
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.SquareConePostcomp

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma exists_arrowPullbackSquare {X : SSet.{u}} [Quasicategory X] [HasFiniteLimits X]
    (r : (horn 2 2 : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X,
      pullbackCospan Q = r ∧ IsPullbackSquare Q ∧
        IsPullbackSquare (Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) ∧
          IsPullbackSquare (Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) := by
  have := hasFiniteLimits_functorCategory (Δ[1] : SSet.{u}) X
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit r
  have hQ := coneSquare_isPullback c hc
  exact ⟨coneSquare c, coneSquare_cospan c, hQ, (isPullbackSquare_arrow_iff _).mp hQ⟩

end SerrePositivity.InfinityCategories
