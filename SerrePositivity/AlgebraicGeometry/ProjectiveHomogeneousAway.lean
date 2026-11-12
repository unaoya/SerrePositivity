module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
概要：次数零の斉次局所化を、通常の加群局所化の中の部分加群と比較する。
方針：二つの局所化の普遍性で通常の局所化を同一視し、斉次分数の全射性を使う。
規約：分母は任意の自然数次数の斉次元とする。
使われ方：Proj の標準開の切断と、有限性を計算した次数付き加群の Čech 項を結ぶ。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (G : ℕ → Submodule R S) [GradedRing G]

/-- 斉次局所化の係数環の作用は加群の公理を満たす。 -/
@[instance_reducible]
def projectiveHomogeneousAwayModule (f : S) : Module R (HomogeneousLocalization.Away G f) :=
  Function.Injective.module R
    { toFun := HomogeneousLocalization.val
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
    (HomogeneousLocalization.val_injective (Submonoid.powers f))
    (HomogeneousLocalization.val_smul (Submonoid.powers f))

local instance (f : S) : Module R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayModule G f

/-- 通常の環局所化と、環を自己加群と見た加群局所化の比較。 -/
def projectiveSelfLocalizationLinearEquiv (f : S) :
    LocalizedModule (Submonoid.powers f) S ≃ₗ[R] Localization.Away f :=
  (IsLocalizedModule.iso (Submonoid.powers f)
    (Algebra.linearMap S (Localization.Away f))).restrictScalars R

/-- 通常の局所化の比較は分子と分母を保つ。 -/
theorem projectiveSelfLocalizationLinearEquiv_mk (f : S) (x : S)
    (s : Submonoid.powers f) :
    projectiveSelfLocalizationLinearEquiv (R := R) f (LocalizedModule.mk x s) =
      Localization.mk x s := by
  change IsLocalizedModule.mk' (Algebra.linearMap S (Localization.Away f)) x s = _
  rw [← IsLocalization.mk'_eq_mk', Localization.mk_eq_mk']

/-- 斉次局所化から通常の加群局所化への単射な線形写像。 -/
def projectiveHomogeneousAwayToModule (f : S) :
    HomogeneousLocalization.Away G f →ₗ[R] LocalizedModule (Submonoid.powers f) S :=
  (projectiveSelfLocalizationLinearEquiv (R := R) f).symm.toLinearMap.comp
    (show HomogeneousLocalization.Away G f →ₗ[R] Localization.Away f from
      { toFun := HomogeneousLocalization.val
        map_add' := HomogeneousLocalization.val_add
        map_smul' := fun r z ↦ HomogeneousLocalization.val_smul (Submonoid.powers f) r z })

/-- 斉次局所化の分数は、加群局所化でも同じ分数に写る。 -/
theorem projectiveHomogeneousAwayToModule_mk {f : S} {k : ℕ} (hf : f ∈ G k)
    (n : ℕ) (x : S) (hx : x ∈ G (n • k)) :
    projectiveHomogeneousAwayToModule G f (HomogeneousLocalization.Away.mk G hf n x hx) =
      LocalizedModule.mk x (projDenominator f n) := by
  apply (projectiveSelfLocalizationLinearEquiv (R := R) f).injective
  simp only [projectiveHomogeneousAwayToModule, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    HomogeneousLocalization.Away.val_mk, projectiveSelfLocalizationLinearEquiv_mk]
  rfl

/-- 次数零の斉次局所化を、通常の局所化の中の斉次分数の部分加群と同一視する。 -/
def projectiveHomogeneousAwayLinearEquiv {f : S} {k : ℕ} (hf : f ∈ G k) :
    HomogeneousLocalization.Away G f ≃ₗ[R]
      projectiveGradedAway f (fun n ↦ G (n • k)) := by
  let L := projectiveHomogeneousAwayToModule G f
  have hmem (z : HomogeneousLocalization.Away G f) :
      L z ∈ projectiveGradedAway f (fun n ↦ G (n • k)) := by
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective G hf z
    apply le_iSup (fun n ↦ LinearMap.range (projectiveGradedFraction f (fun n ↦ G (n • k)) n)) n
    refine LinearMap.mem_range.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [projectiveGradedFraction_apply]
    exact (projectiveHomogeneousAwayToModule_mk G hf n x hx).symm
  let l := L.codRestrict _ hmem
  apply LinearEquiv.ofBijective l
  constructor
  · intro x y h
    apply (HomogeneousLocalization.val_injective (Submonoid.powers f))
    have he := congrArg (projectiveSelfLocalizationLinearEquiv (R := R) f)
      (congrArg Subtype.val h)
    simpa [l, L, projectiveHomogeneousAwayToModule] using he
  · intro z
    have hstep (n : ℕ) (m : G (n • k)) : f • m.val ∈ G ((n + 1) • k) := by
      change f * m.val ∈ G ((n + 1) • k)
      simpa only [succ_nsmul, add_comm] using
        SetLike.mul_mem_graded hf m.property
    obtain ⟨n, x, hx⟩ := (mem_projectiveGradedAway_iff f (fun n ↦ G (n • k)) hstep z.val).mp z.property
    refine ⟨HomogeneousLocalization.Away.mk G hf n x.val x.property, ?_⟩
    apply Subtype.ext
    change L _ = z.val
    rw [projectiveHomogeneousAwayToModule_mk G hf, ← hx, projectiveGradedFraction_apply]

/-- 斉次局所化から加群局所化への比較は、標準開を狭める写像と可換。 -/
theorem projectiveHomogeneousAwayToModule_restriction
    {f g t : S} {i j : ℕ} (hf : f ∈ G i) (hg : g ∈ G j) (ht : t = f * g)
    (z : HomogeneousLocalization.Away G f) :
    projectiveHomogeneousAwayToModule G t (HomogeneousLocalization.awayMap G hg ht z) =
      projectiveModuleAwayRestriction (M := S) (show f ∣ t from ⟨g, ht⟩)
        (projectiveHomogeneousAwayToModule G f z) := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective G hf z
  rw [HomogeneousLocalization.awayMap_mk, projectiveHomogeneousAwayToModule_mk,
    projectiveHomogeneousAwayToModule_mk, projectiveModuleAwayRestriction_mk ht]
  congr 1
  exact mul_comm x (g ^ n)

end SerrePositivity.AlgebraicGeometry
