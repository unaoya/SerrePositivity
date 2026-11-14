module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization
public import Mathlib.RingTheory.Ideal.Operations

/-!
概要：斉次局所化で分子の族をイデアル倍にする操作は、局所化後の成分のイデアル倍になる。
方針：分数の線形写像の像と、イデアル倍・上限との交換を用いる。
規約：分母の非零性、flat、有限生成性を仮定しない。
使われ方：閉厚化の標準開の係数を、Iⁿ による商として比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (I : Ideal R) (f : S) (V : ℕ → Submodule R M)

/-- 指数を固定した分数のイデアル倍の像は、元の像のイデアル倍。 -/
theorem projectiveGradedFraction_ideal_range (n : ℕ) :
    LinearMap.range (projectiveGradedFraction f (fun n ↦ I • V n) n) =
      I • LinearMap.range (projectiveGradedFraction f V n) := by
  simp only [projectiveGradedFraction, LinearMap.range_comp,
    Submodule.range_subtype, Submodule.map_smul'']

/-- 分子の各成分のイデアル倍を局所化すると、局所化の指定成分のイデアル倍になる。 -/
theorem projectiveGradedAway_ideal_smul :
    projectiveGradedAway f (fun n ↦ I • V n) = I • projectiveGradedAway f V := by
  simp only [projectiveGradedAway, projectiveGradedFraction_ideal_range, Submodule.smul_iSup]

end SerrePositivity.AlgebraicGeometry
