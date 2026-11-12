module

public import SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarLocalization
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
概要：任意の加群について、局所化の係数環の変更を分子の指定次数成分へ制限する。
方針：各斉次分数の比較を、分数の像の上限の比較へ移す。
規約：環の局所化に限らず、両方の係数環上の加群を許す。
使われ方：Rees 加群の P 上と B[X] 上の Proj 次数零のチャートを比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

variable {R P Q M : Type*} [CommRing R] [CommRing P] [CommRing Q]
variable [Algebra R P] [Algebra P Q] [Algebra R Q] [IsScalarTower R P Q]
variable [AddCommGroup M] [Module R M] [Module P M] [Module Q M]
variable [IsScalarTower R P M] [IsScalarTower R Q M] [IsScalarTower P Q M]

/-- 分子の各部分加群を指定した局所化も、係数環の変更で同一視できる。 -/
def projectiveModuleScalarGradedAwayLinearEquiv (f : P) (V : ℕ → Submodule R M) :
    projectiveGradedAway f V ≃ₗ[R] projectiveGradedAway (algebraMap P Q f) V := by
  let e := projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) (M := M) f
  have hfrac (n : ℕ) (x : V n) :
      e (projectiveGradedFraction f V n x) =
        projectiveGradedFraction (algebraMap P Q f) V n x := by
    simp only [projectiveGradedFraction_apply]
    rw [projectiveModuleScalarLocalizationLinearEquiv_mk]
    congr 1
    apply Subtype.ext
    exact map_pow (algebraMap P Q) f n
  have hmap : (projectiveGradedAway f V).map e.toLinearMap =
      projectiveGradedAway (algebraMap P Q f) V := by
    rw [projectiveGradedAway, Submodule.map_iSup, projectiveGradedAway]
    congr 1
    funext n
    apply Submodule.ext
    intro z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
      exact LinearMap.mem_range.mpr ⟨x, (hfrac n x).symm⟩
    · intro hz
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
      exact Submodule.mem_map.mpr ⟨projectiveGradedFraction f V n x,
        LinearMap.mem_range_self _ x, hfrac n x⟩
  exact e.ofSubmodules _ _ hmap

/-- 斉次成分の比較も、通常の局所化の比較と同じ元を与える。 -/
theorem projectiveModuleScalarGradedAwayLinearEquiv_val (f : P) (V : ℕ → Submodule R M)
    (z : projectiveGradedAway f V) :
    (projectiveModuleScalarGradedAwayLinearEquiv (R := R) (Q := Q) f V z).val =
      projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) f z.val := rfl

end SerrePositivity.AlgebraicGeometry
