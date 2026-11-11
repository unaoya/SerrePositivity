module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechModuleMap
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechInverseSystem
public import SerrePositivity.AlgebraicGeometry.AdicProjectionNaturality

/-!
概要：実際の次数付き加群写像に対する、Čech 形式関数の自然性。
方針：実際の射影・遷移の可換性を、完備化比較の自然性へ代入する。
規約：flat 性を仮定せず、基底環とイデアルを固定する。
使われ方：M→M/JM に適用して、非 flat な閉厚化との整合性を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M N : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (I : Ideal R) (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : M →ₗ[MvPolynomial ι R] N) (hf : ∀ j, ∀ x ∈ G j, f x ∈ H j)

/-- 実際の次数付き加群写像が誘導する、閉厚化の Čech 逆系の間の自然変換。 -/
def reesAdicProjectiveClosedCechModuleNatTrans (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechInverseSystem (ι := ι) I G d q ⟶
      reesAdicProjectiveClosedCechInverseSystem (ι := ι) I H d q where
  app n := reesAdicProjectiveClosedCechModuleMap I G H f hf n.unop d q
  naturality i j g := (reesAdicProjectiveClosedCechModuleMap_transition
    I G H f hf i.unop j.unop (leOfHom g.unop) d q).symm

/-- 実際の次数付き加群写像が誘導する、閉厚化の Čech 互換族の間の線形写像。 -/
def reesAdicProjectiveClosedCechModuleFamiliesMap (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q →ₗ[R]
      reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I H d q :=
  compatibleLinearFamiliesMap
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I H i j h d q).hom)
    (fun n ↦ (reesAdicProjectiveClosedCechModuleMap I G H f hf n d q).hom)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesAdicProjectiveClosedCechModuleMap_transition I G H f hf i j h d q))

/-- 完備化からの標準 Čech 写像は、実際の次数付き加群写像と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechCompletionMap_module_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesAdicProjectiveClosedCechModuleFamiliesMap I G H f hf d q
        (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G d q a) =
      reesAdicProjectiveClosedCechCompletionMap (ι := ι) I H d q
        (AdicCompletion.map I (projectiveNatGradedModuleCechHomologyMap G H f hf d q).hom a) :=
  adicProjectionCompletionMap_naturality_apply I
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom)
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I H n d q).hom)
    (fun n ↦ reesAdicProjectiveClosedCechProjection_pow_le_ker (ι := ι) I G n d q)
    (fun n ↦ reesAdicProjectiveClosedCechProjection_pow_le_ker (ι := ι) I H n d q)
    (projectiveNatGradedModuleCechHomologyMap G H f hf d q).hom
    (fun n ↦ (reesAdicProjectiveClosedCechModuleMap I G H f hf n d q).hom)
    (fun n ↦ congrArg ModuleCat.Hom.hom
      (reesAdicProjectiveClosedCechModuleMap_projection I G H f hf n d q))
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I H i j h d q).hom)
    (fun i j h ↦ reesAdicProjectiveClosedCechProjection_linear_compat (ι := ι) I G i j h d q)
    (fun i j h ↦ reesAdicProjectiveClosedCechProjection_linear_compat (ι := ι) I H i j h d q)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesAdicProjectiveClosedCechModuleMap_transition I G H f hf i j h d q)) a

variable [IsNoetherianRing R]
variable [Module.Finite (MvPolynomial ι R) M] [Module.Finite (MvPolynomial ι R) N]

/-- Čech 形式関数の同型は、実際の次数付き加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechCompletionLinearEquiv_module_naturality
    (d : ℤ) (q : ℕ) (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesAdicProjectiveClosedCechModuleFamiliesMap I G H f hf d q
        (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G d q a) =
      reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I H d q
        (AdicCompletion.map I (projectiveNatGradedModuleCechHomologyMap G H f hf d q).hom a) := by
  change reesAdicProjectiveClosedCechModuleFamiliesMap I G H f hf d q
      (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G d q a) =
    reesAdicProjectiveClosedCechCompletionMap (ι := ι) I H d q
      (AdicCompletion.map I (projectiveNatGradedModuleCechHomologyMap G H f hf d q).hom a)
  exact reesAdicProjectiveClosedCechCompletionMap_module_naturality I G H f hf d q a

end SerrePositivity.AlgebraicGeometry
