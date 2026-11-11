module

public import SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumSubmodule
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumComponents
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
概要：局所化と直和の比較を、分子の指定次数成分へ制限する。
方針：順方向は分数の各成分で判定し、逆方向は有限台の各成分を持ち上げる。
規約：分母を一つ掛けると分子の指定部分が次の段に入ることを仮定する。
使われ方：Rees 加群の Proj 次数零の局所化と、各 IⁿM のチャートの直和の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum
attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq κ]
variable {M : κ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)]
variable (f : S) (V : ∀ i, ℕ → Submodule R (M i))

/-- 局所化と直和の同値は、指定次数の分子からなる部分加群を対応させる。 -/
theorem projectiveGradedLocalizedDirectSum_map
    (hstep : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1)) :
    (projectiveGradedAway f (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k))).map
        ((projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M).restrictScalars R).toLinearMap =
      projectiveDirectSumSubmodule (fun i ↦ projectiveGradedAway f (V i)) := by
  let W := fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k)
  have hW (k : ℕ) (m : W k) : f • m.val ∈ W (k + 1) := by
    rw [mem_projectiveDirectSumSubmodule]
    intro i
    exact hstep i k ⟨m.val i, (mem_projectiveDirectSumSubmodule _ _).mp m.property i⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_projectiveDirectSumSubmodule]
    obtain ⟨k, m, rfl⟩ := (mem_projectiveGradedAway_iff f W hW z).mp hz
    intro i
    apply (le_iSup (fun k ↦ LinearMap.range (projectiveGradedFraction f (V i) k)) k)
    refine LinearMap.mem_range.mpr ⟨⟨m.val i,
      (mem_projectiveDirectSumSubmodule _ _).mp m.property i⟩, ?_⟩
    simp only [projectiveGradedFraction_apply]
    exact (projectiveLocalizedDirectSumLinearEquiv_mk_component
      (Submonoid.powers f) M m.val (projDenominator f k) i).symm
  · intro y hy
    rw [← projectiveDirectSumSubmodule_range] at hy
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
    clear hy
    induction z using DirectSum.induction_on with
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | of i z =>
      obtain ⟨k, m, hm⟩ := (mem_projectiveGradedAway_iff f (V i) (hstep i) z.val).mp z.property
      let x : ⨁ i, M i := DirectSum.of M i m.val
      have hx : x ∈ W k := by
        rw [mem_projectiveDirectSumSubmodule]
        intro j
        by_cases hij : i = j
        · subst j
          simpa [x] using m.property
        · simpa [x, DirectSum.of_apply, hij] using (V j k).zero_mem
      refine Submodule.mem_map.mpr ⟨projectiveGradedFraction f W k ⟨x, hx⟩,
        (le_iSup (fun k ↦ LinearMap.range (projectiveGradedFraction f W k)) k)
          (LinearMap.mem_range_self (projectiveGradedFraction f W k) ⟨x, hx⟩), ?_⟩
      apply DFinsupp.ext
      intro j
      change (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M
        (projectiveGradedFraction f W k ⟨x, hx⟩)) j = _
      rw [projectiveGradedFraction_apply, projectiveLocalizedDirectSumLinearEquiv_mk_component,
        DirectSum.lmap_of]
      change LocalizedModule.mk (x j) (projDenominator f k) =
        (DirectSum.of (fun i ↦ LocalizedModule (Submonoid.powers f) (M i)) i z.val) j
      by_cases hij : i = j
      · subst j
        simpa [x, projectiveGradedFraction_apply] using hm
      · simp [x, DirectSum.of_apply, hij]

/-- 指定次数の斉次局所化と、その各成分の斉次局所化の直和の線形同値。 -/
def projectiveGradedLocalizedDirectSumLinearEquiv
    (hstep : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1)) :
    projectiveGradedAway f (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k)) ≃ₗ[R]
      ⨁ i, projectiveGradedAway f (V i) :=
  (((projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M).restrictScalars R).ofSubmodules
    _ _ (projectiveGradedLocalizedDirectSum_map f V hstep)).trans
      (projectiveDirectSumSubmoduleLinearEquiv (fun i ↦ projectiveGradedAway f (V i))).symm

/-- 斉次局所化の直和比較は、周囲の加群の局所化比較に一致する。 -/
theorem projectiveGradedLocalizedDirectSumLinearEquiv_val
    (hstep : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1))
    (z : projectiveGradedAway f (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k))) :
    DirectSum.lmap (fun i ↦ (projectiveGradedAway f (V i)).subtype)
        (projectiveGradedLocalizedDirectSumLinearEquiv f V hstep z) =
      projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M z.val := by
  have h := projectiveDirectSumSubmoduleLinearEquiv_val
    (fun i ↦ projectiveGradedAway f (V i))
    (projectiveGradedLocalizedDirectSumLinearEquiv f V hstep z)
  rw [← h]
  change ((projectiveDirectSumSubmoduleLinearEquiv (fun i ↦ projectiveGradedAway f (V i)))
    ((projectiveDirectSumSubmoduleLinearEquiv (fun i ↦ projectiveGradedAway f (V i))).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end SerrePositivity.AlgebraicGeometry
