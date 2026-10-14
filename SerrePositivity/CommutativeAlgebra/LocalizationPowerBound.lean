module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # 局所化で消える有限生成加群の一様な冪による零化 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有限生成加群の各元をgのある冪が消せば、一つの共通冪が全加群を消す。 -/
theorem exists_uniform_pow_smul_zero [Module.Finite R M] (g : R)
    (h : ∀ x : M, ∃ n : ℕ, g ^ n • x = 0) :
    ∃ n : ℕ, ∀ x : M, g ^ n • x = 0 := by
  classical
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' R M
  let b := Pi.basisFun R (Fin r)
  choose n hn using fun i : Fin r ↦ h (f (b i))
  let N := Finset.univ.sup n
  have hzero : g ^ N • f = 0 := by
    apply b.ext
    intro i
    change g ^ N • f (b i) = 0
    have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    rw [show N = (N - n i) + n i by omega, pow_add, mul_smul, hn i, smul_zero]
  refine ⟨N, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := hf x
  change (g ^ N • f) y = 0
  rw [hzero]
  rfl

/-- 主元局所化で零になる一つの元は、その元の冪で消える。 -/
theorem exists_pow_smul_zero_of_localized_zero (g : R) (x : M)
    (hx : LocalizedModule.mkLinearMap (Submonoid.powers g) M x = 0) :
    ∃ n : ℕ, g ^ n • x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)).mp hx
  exact ⟨n, hn⟩

/-- 局所化で零になる有限生成加群は、一様なg冪で零化される。 -/
theorem exists_uniform_pow_smul_zero_of_localization [Module.Finite R M] (g : R)
    (h : ∀ x : M, LocalizedModule.mkLinearMap (Submonoid.powers g) M x = 0) :
    ∃ n : ℕ, ∀ x : M, g ^ n • x = 0 :=
  exists_uniform_pow_smul_zero g (fun x ↦ exists_pow_smul_zero_of_localized_zero g x (h x))

/-- 主元局所化で誘導される加群写像。 -/
abbrev awayModuleMap {N : Type*} [AddCommGroup N] [Module R N]
    (g : R) (f : M →ₗ[R] N) :=
  IsLocalizedModule.map (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) f

/-- 局所化した写像が全射なら、余核の各元はg冪ねじれである。 -/
theorem exists_pow_smul_mem_range_of_away_surjective
    {N : Type*} [AddCommGroup N] [Module R N] (g : R) (f : M →ₗ[R] N)
    (hf : Function.Surjective (awayModuleMap g f)) (y : N) :
    ∃ n : ℕ, g ^ n • y ∈ LinearMap.range f := by
  let ιM := LocalizedModule.mkLinearMap (Submonoid.powers g) M
  let ιN := LocalizedModule.mkLinearMap (Submonoid.powers g) N
  obtain ⟨z, hz⟩ := hf (ιN y)
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj ιM g z
  have heq : ιN (g ^ n • y - f x) = 0 := by
    rw [map_sub, map_smul]
    have hh := congrArg (awayModuleMap g f) hx
    change g ^ n • ιN y - ιN (f x) = 0
    change awayModuleMap g f (g ^ n • z) = awayModuleMap g f (ιM x) at hh
    simpa only [map_smul, hz, ιM, ιN, awayModuleMap,
      IsLocalizedModule.map_apply, sub_eq_zero] using hh
  obtain ⟨k, hk⟩ := exists_pow_smul_zero_of_localized_zero g _ heq
  refine ⟨k + n, ?_⟩
  refine ⟨g ^ k • x, ?_⟩
  rw [map_smul]
  rw [smul_sub, sub_eq_zero] at hk
  simpa only [pow_add, mul_smul] using hk.symm

/-- 有限生成な余核のg冪ねじれには一様な指数が存在する。 -/
theorem exists_uniform_pow_smul_coker_zero_of_away_surjective
    {N : Type*} [AddCommGroup N] [Module R N]
    (g : R) (f : M →ₗ[R] N) [Module.Finite R (N ⧸ LinearMap.range f)]
    (hf : Function.Surjective (awayModuleMap g f)) :
    ∃ n : ℕ, ∀ x : N ⧸ LinearMap.range f, g ^ n • x = 0 := by
  apply exists_uniform_pow_smul_zero g
  intro x
  obtain ⟨y, rfl⟩ := (LinearMap.range f).mkQ_surjective x
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_range_of_away_surjective g f hf y
  refine ⟨n, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr hn

end SerrePositivity
