module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 冪で零化される加群の導来完備性

加群を零次数に置いた実導来対象について、`f` のある冪で加群が零化されれば
局所化加群からの全次数の射が消えることを証明する。標数や有限生成性は仮定しない。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.DerivedCompletion

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- 加群の導来 `f` 完備性：零次数に置いた加群が、局所化からの全次数の射の消滅を満たす。 -/
def IsModuleComplete (f : R) (M : ModuleCat.{u} R) : Prop :=
  IsComplete R f ((moduleObjectFunctor R).obj M)

/-- `f` のある冪が加群のすべての元を零化すれば、加群は導来 `f` 完備。
加群上の零化を自己射の零性へ移し、零次数の導来関手で導来圏の零化を得る。 -/
theorem isModuleComplete_of_pow_smul_zero (f : R) (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ m : M, (f ^ N) • m = 0) : IsModuleComplete R f M := by
  have hzero : (f ^ N) • 𝟙 M = 0 := by
    ext m
    exact hM m
  apply isComplete_of_scalar_pow_zero R f _ N
  have h := congrArg ((moduleObjectFunctor R).map) hzero
  simpa using h

/-- 自然数 `p` の冪で零化される加群は、環に写した `p` に関して導来完備。
素数性の仮定は不要であり、通常の `p` 冪 torsion 加群を直接扱える。 -/
theorem isModuleComplete_of_natCast_pow_smul_zero (p N : ℕ) (M : ModuleCat.{u} R)
    (hM : ∀ m : M, ((p : R) ^ N) • m = 0) :
    IsModuleComplete R (p : R) M :=
  isModuleComplete_of_pow_smul_zero R (p : R) M N hM

/-- イデアルが `f` の冪を含めば、その商環を基底環の加群とみたものは導来 `f` 完備。
商環への像が零であることから加群の零化条件を得る。 -/
theorem isModuleComplete_quotient_of_pow_mem (f : R) (I : Ideal R) (N : ℕ)
    (hN : f ^ N ∈ I) : IsModuleComplete R f (ModuleCat.of R (R ⧸ I)) := by
  apply isModuleComplete_of_pow_smul_zero R f _ N
  intro m
  have hzero : algebraMap R (R ⧸ I) (f ^ N) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hN
  change algebraMap R (R ⧸ I) (f ^ N) * m = 0
  rw [hzero, zero_mul]

/-- `f` の冪で生成される主イデアルによる商環は、導来 `f` 完備。
特に自然数 `p` の環への像を代入して `R/(p^N)` に適用できる。 -/
theorem isModuleComplete_quotient_span_pow (f : R) (N : ℕ) :
    IsModuleComplete R f (ModuleCat.of R (R ⧸ Ideal.span {f ^ N})) := by
  apply isModuleComplete_quotient_of_pow_mem R f _ N
  exact Ideal.subset_span (Set.mem_singleton _)

end SerrePositivity.DerivedCompletion
