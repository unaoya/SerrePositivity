module
public import SerrePositivity.InfinityCategories.Stable.FunctorFiniteLimits
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Core.FiniteShapes
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

lemma isPullbackSquare_functor_iff {K X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X) :
    IsPullbackSquare Q ↔ ∀ k : K _⦋0⦌, IsPullbackSquare (Q ≫ evaluateFunctorAt k) := by
  have hp : HasPointwiseLimits (pullbackCospan Q) := fun _ ↦ HasFiniteLimits.hasLimit _
  constructor
  · intro h k
    have hk := isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits hp
      (pullbackCone Q) h k
    exact (F2.isLimitCone_map_pullbackCone_iff (evaluateFunctorAt k) Q).mp hk
  · intro h
    apply isLimitCone_of_pointwise
    intro k
    exact (F2.isLimitCone_map_pullbackCone_iff (evaluateFunctorAt k) Q).mpr (h k)

lemma isPullbackSquare_arrow_iff {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    IsPullbackSquare Q ↔
      IsPullbackSquare (Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) ∧
        IsPullbackSquare (Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) := by
  rw [isPullbackSquare_functor_iff]
  constructor
  · intro h
    exact ⟨h _, h _⟩
  · rintro ⟨h0, h1⟩ k
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
    fin_cases i
    · exact h0
    · exact h1

end SerrePositivity.InfinityCategories
