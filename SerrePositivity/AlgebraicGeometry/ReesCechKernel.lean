module

public import SerrePositivity.AlgebraicGeometry.ReesCechImageAssembly
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：実際の Čech 包含の核の直和を、有限な Rees 部分加群として扱う。
方針：像への Rees 全射の核を成分ごとに計算し、斉次な核の元で生成する。
規約：有限性には Noether 基底と多項式環上の有限生成性を使う。
使われ方：核の斉次生成元の次数を一様に抑え、遷移の零化へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesCechKernelModule (d : ℤ) (q : ℕ) :
    Module (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
  reesAdicCechIntegerDirectSumTransportedModule (ι := ι) I G d q

/-- Čech 像への Rees 全射の核。各段の包含の核をまとめる。 -/
def reesAdicProjectiveCechKernel (d : ℤ) (q : ℕ) :
    Submodule (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
  LinearMap.ker (reesAdicProjectiveCechImageAssemble (ι := ι) I G d q)

/-- Rees 核への所属は、各成分が実際の Čech 包含で零になることと同値。 -/
theorem reesAdicProjectiveCechKernel_mem_iff (d : ℤ) (q : ℕ)
    (x : ReesIntegerCechDirectSum (ι := ι) I G d q) :
    x ∈ reesAdicProjectiveCechKernel (ι := ι) I G d q ↔
      ∀ n, (reesAdicProjectiveCechToModule (ι := ι) I G n d q).hom (x n) = 0 := by
  let F := reesAdicProjectiveCechImageFiltration (ι := ι) I G d q
  let f := fun n ↦ reesAdicProjectiveCechImageStageMap (ι := ι) I G n d q
  constructor
  · intro hx
    change reesFiltrationDirectSumLinearEquiv F (DirectSum.lmap f x) = 0 at hx
    have h0 : DirectSum.lmap f x = 0 :=
      (reesFiltrationDirectSumLinearEquiv F).injective (by simpa only [map_zero] using hx)
    intro n
    exact congrArg Subtype.val (DFunLike.congr_fun h0 n)
  · intro hx
    change reesFiltrationAssemble F (DirectSum.lmap f x) = 0
    have h0 : DirectSum.lmap f x = 0 := by
      apply DFinsupp.ext
      intro n
      apply Subtype.ext
      exact hx n
    rw [h0, map_zero]

/-- 一つの斉次成分の Rees 核への所属は、その Čech 包含での零化と同値。 -/
theorem reesAdicProjectiveCechKernel_lof_mem_iff (n : ℕ) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G n d q) :
    DirectSum.lof R ℕ
      (fun j ↦ reesAdicProjectiveCechStage (ι := ι) I G j d q) n x ∈
        reesAdicProjectiveCechKernel (ι := ι) I G d q ↔
      (reesAdicProjectiveCechToModule (ι := ι) I G n d q).hom x = 0 := by
  rw [reesAdicProjectiveCechKernel_mem_iff]
  constructor
  · intro hx
    simpa only [DirectSum.lof_apply] using hx n
  · intro hx j
    by_cases h : n = j
    · subst j
      simpa only [DirectSum.lof_apply] using hx
    · simp [DirectSum.lof_eq_of, DirectSum.of_apply, h]

/-- 各段の実際の Čech 核の元を、一つの直和成分に入れた集合。 -/
def reesAdicProjectiveCechKernelHomogeneous (d : ℤ) (q : ℕ) :
    Set (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
  {z | ∃ n, ∃ x : reesAdicProjectiveCechStage (ι := ι) I G n d q,
    (reesAdicProjectiveCechToModule (ι := ι) I G n d q).hom x = 0 ∧
      z = DirectSum.lof R ℕ
        (fun j ↦ reesAdicProjectiveCechStage (ι := ι) I G j d q) n x}

/-- 実際の Čech 核の Rees 加群は、その斉次な核の元で生成される。 -/
theorem reesAdicProjectiveCechKernel_span_homogeneous (d : ℤ) (q : ℕ) :
    Submodule.span (reesAlgebra I) (reesAdicProjectiveCechKernelHomogeneous (ι := ι) I G d q) =
      reesAdicProjectiveCechKernel (ι := ι) I G d q := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨n, x, hx, rfl⟩
    exact (reesAdicProjectiveCechKernel_lof_mem_iff (ι := ι) I G n d q x).mpr hx
  · intro x hx
    have hn := (reesAdicProjectiveCechKernel_mem_iff (ι := ι) I G d q x).mp hx
    rw [← DirectSum.sum_support_of x]
    apply Submodule.sum_mem
    intro n _hn
    apply Submodule.subset_span
    exact ⟨n, x n, hn n, rfl⟩

/-- Čech 核の Rees 加群は有限生成。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に使う核の有限性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechKernel_finite [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    Module.Finite (reesAlgebra I) (reesAdicProjectiveCechKernel (ι := ι) I G d q) := by
  letI := reesAdicCechIntegerDirectSumFinite (ι := ι) I G d q
  infer_instance

/-- 実際の Čech 核には有限個の斉次生成元を選べる。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechKernel_finite_homogeneous_generators [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    ∃ s : Finset (ReesIntegerCechDirectSum (ι := ι) I G d q),
      (↑s : Set _) ⊆ reesAdicProjectiveCechKernelHomogeneous (ι := ι) I G d q ∧
        Submodule.span (reesAlgebra I) (↑s : Set _) =
          reesAdicProjectiveCechKernel (ι := ι) I G d q := by
  have hfg := (Module.Finite.iff_fg.mp
    (reesAdicProjectiveCechKernel_finite (ι := ι) I G d q))
  rw [← reesAdicProjectiveCechKernel_span_homogeneous (ι := ι) I G d q] at hfg
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  exact ⟨s, hs, hspan.symm.trans
    (reesAdicProjectiveCechKernel_span_homogeneous (ι := ι) I G d q)⟩

end SerrePositivity.AlgebraicGeometry
