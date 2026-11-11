module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarLocalization
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousAway
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
概要：係数環の加群局所化と代数の局所化の比較を、斉次分数の成分へ制限する。
方針：各固定分母の分数を比較し、その像の上限を線形同型で写す。
規約：許された分子の族は、同じ代数の部分加群として与える。
使われ方：多項式加群として計算した次数零成分を Proj の標準開へ移す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]

/-- 係数環と代数の二つの加群局所化を、同じ環局所化を経由して比較する。 -/
def projectiveScalarModuleAwayLinearEquiv (f : P) :
    LocalizedModule (Submonoid.powers f) S ≃ₗ[R]
      LocalizedModule (Submonoid.powers (algebraMap P S f)) S :=
  (projectiveScalarLocalizationLinearEquiv (R := R) (S := S) f).trans
    (projectiveSelfLocalizationLinearEquiv (R := R) (algebraMap P S f)).symm

/-- 係数環を変える局所化の比較は、分母の冪と分子を保つ。 -/
theorem projectiveScalarModuleAwayLinearEquiv_mk (f : P) (n : ℕ) (x : S) :
    projectiveScalarModuleAwayLinearEquiv (R := R) (S := S) f
        (LocalizedModule.mk x (projDenominator f n)) =
      LocalizedModule.mk x (projDenominator (algebraMap P S f) n) := by
  apply (projectiveSelfLocalizationLinearEquiv (R := R) (algebraMap P S f)).injective
  change projectiveSelfLocalizationLinearEquiv (R := R) (algebraMap P S f)
      ((projectiveSelfLocalizationLinearEquiv (R := R) (algebraMap P S f)).symm
        (projectiveScalarLocalizationLinearEquiv (R := R) (S := S) f
          (LocalizedModule.mk x (projDenominator f n)))) = _
  rw [LinearEquiv.apply_symm_apply, projectiveScalarLocalizationLinearEquiv_mk,
    projectiveSelfLocalizationLinearEquiv_mk]
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap P S) f n

/-- 分子の各部分加群を指定した局所化も、係数環の変更で同一視できる。 -/
def projectiveScalarGradedAwayLinearEquiv (f : P) (V : ℕ → Submodule R S) :
    projectiveGradedAway f V ≃ₗ[R] projectiveGradedAway (algebraMap P S f) V := by
  let e := projectiveScalarModuleAwayLinearEquiv (R := R) (S := S) f
  have hfrac (n : ℕ) (x : V n) :
      e (projectiveGradedFraction f V n x) =
        projectiveGradedFraction (algebraMap P S f) V n x := by
    simp only [projectiveGradedFraction_apply]
    exact projectiveScalarModuleAwayLinearEquiv_mk f n x.val
  have hmap : (projectiveGradedAway f V).map e.toLinearMap =
      projectiveGradedAway (algebraMap P S f) V := by
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
theorem projectiveScalarGradedAwayLinearEquiv_val (f : P) (V : ℕ → Submodule R S)
    (z : projectiveGradedAway f V) :
    (projectiveScalarGradedAwayLinearEquiv (R := R) f V z).val =
      projectiveScalarModuleAwayLinearEquiv (R := R) f z.val := rfl

end SerrePositivity.AlgebraicGeometry
