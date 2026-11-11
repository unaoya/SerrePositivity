module

public import SerrePositivity.AlgebraicGeometry.ReesCechImageAssembly
public import SerrePositivity.AlgebraicGeometry.ProjectiveFormalFunctionsFiltration

/-!
概要：実際の射影 Čech 像の Rees 加群の有限性と I 進評価を示す。
方針：コホモロジーの直和の有限性を全射で移し、安定フィルトレーションを使う。
規約：基底は Noether、元の次数付き加群は多項式環上有限とする。
使われ方：閉厚化への Čech 写像の核の評価を、長完全列と合わせて得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) M]

/-- 各 IⁿM からの Čech 像の Rees 加群は有限生成。
原典 Stacks 30.20.4(1) の Hⁱ の核の評価に用いる有限性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechImageRees_finite (d : ℤ) (q : ℕ) :
    Module.Finite (reesAlgebra I)
      (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q).submodule := by
  letI : Module (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
    reesAdicCechIntegerDirectSumTransportedModule (ι := ι) I G d q
  letI := reesAdicCechIntegerDirectSumFinite (ι := ι) I G d q
  exact Module.Finite.of_surjective
    (reesAdicProjectiveCechImageAssemble (ι := ι) I G d q)
    (reesAdicProjectiveCechImageAssemble_surjective (ι := ι) I G d q)

/-- Čech 版の実際の像の一様な I 進評価。
原典 Stacks 30.20.4(1) の Hⁱ の核の評価に渡す像の評価であり、
閉厚化への写像の核との同定は長完全列による別の段階とする。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechImage_bound (d : ℤ) (q : ℕ) :
    ∃ c : ℕ, ∀ n, c ≤ n →
      reesAdicProjectiveCechImage (ι := ι) I G n d q ≤
        I ^ (n - c) • (⊤ : Submodule R
          (reesAdicProjectiveCechTarget (ι := ι) G d q)) := by
  letI : Module.Finite R (reesAdicProjectiveCechTarget (ι := ι) G d q) :=
    projectiveNatGradedFullCechHomology_finite (ι := ι) G d q
  letI : Module (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
    reesAdicCechIntegerDirectSumTransportedModule (ι := ι) I G d q
  letI := reesAdicCechIntegerDirectSumFinite (ι := ι) I G d q
  exact cechFormalFunctions_filtration_bound_of_finiteReesImage
    (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q)
    (reesAdicProjectiveCechImageAssemble (ι := ι) I G d q)
    (reesAdicProjectiveCechImageAssemble_surjective (ι := ι) I G d q)

/-- Čech 像のフィルトレーションと I 進フィルトレーションは互いに共終。
原典 Stacks 30.20.4(1) の Hⁱ の核の評価に渡す Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechImage_cofinal (d : ℤ) (q : ℕ) :
    (∀ n, I ^ n • (⊤ : Submodule R
      (reesAdicProjectiveCechTarget (ι := ι) G d q)) ≤
        reesAdicProjectiveCechImage (ι := ι) I G n d q) ∧
    (∀ n, ∃ m, reesAdicProjectiveCechImage (ι := ι) I G m d q ≤
      I ^ n • (⊤ : Submodule R
        (reesAdicProjectiveCechTarget (ι := ι) G d q))) := by
  refine ⟨fun n ↦ reesAdicProjectiveCechImage_contains_pow (ι := ι) I G n d q, ?_⟩
  obtain ⟨c, hc⟩ := reesAdicProjectiveCechImage_bound (ι := ι) I G d q
  intro n
  refine ⟨n + c, ?_⟩
  simpa only [Nat.add_sub_cancel] using hc (n + c) (Nat.le_add_left c n)

end SerrePositivity.AlgebraicGeometry
