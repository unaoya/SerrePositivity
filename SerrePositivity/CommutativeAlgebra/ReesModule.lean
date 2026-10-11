module

public import SerrePositivity.CommutativeAlgebra.AssociatedGraded

/-! # I 進 Rees 加群と随伴次数加群の商表示

`⊕ I^nM t^n` を Mathlib の Rees 加群として構成する。
分母 `⊕ I^(n+1)M t^n` による商が随伴次数加群を与える。
有限性は I 進フィルトレーションの安定性から証明する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

open PolynomialModule
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- `⊕ I^nM t^n`。係数が I 進部分加群に入る多項式加群。 -/
abbrev ReesModule := (I.stableFiltration (⊤ : Submodule R M)).submodule

/-- `⊕ I^(n+1)M t^n` の ambient polynomial module 内での表示。 -/
abbrev shiftedReesModule := (I.stableFiltration (I • (⊤ : Submodule R M))).submodule

lemma shiftedReesModule_le : shiftedReesModule R I M ≤ ReesModule R I M := by
  intro f hf n
  exact Submodule.smul_mono le_rfl Submodule.smul_le_right (hf n)

/-- `⊕ I^(n+1)M t^n` を Rees 加群内の部分加群として見る。 -/
def reesDenominator : Submodule (reesAlgebra I) (ReesModule R I M) :=
  (shiftedReesModule R I M).comap (ReesModule R I M).subtype

/-- 随伴次数加群の Rees 加群による商表示。 -/
abbrev ReesGraded := ReesModule R I M ⧸ reesDenominator R I M

lemma mem_reesDenominator (f : ReesModule R I M) :
    f ∈ reesDenominator R I M ↔
      ∀ n, (f : PolynomialModule R M).coeff n ∈ adicSubmodule R I M (n + 1) := by
  change (∀ n, f.1.coeff n ∈ I ^ n • (I • (⊤ : Submodule R M))) ↔ _
  simp only [adicSubmodule, pow_succ, mul_smul]

instance reesModule_finite [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite (reesAlgebra I) (ReesModule R I M) := by
  apply Module.Finite.of_fg
  exact ((I.stableFiltration (⊤ : Submodule R M)).submodule_fg_iff_stable
    (fun _ => IsNoetherian.noetherian _)).mpr (I.stableFiltration_stable _)

instance reesGraded_finite [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite (reesAlgebra I) (ReesGraded R I M) := inferInstance

/-- 随伴次数加群全体も I で消える。 -/
lemma ideal_le_annihilator_reesGraded :
    I ≤ Module.annihilator R (ReesGraded R I M) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨f, rfl⟩ := (reesDenominator R I M).mkQ_surjective x
  have hf : a • f ∈ reesDenominator R I M := by
    rw [mem_reesDenominator]
    intro n
    change a • f.1.coeff n ∈ I ^ (n + 1) • (⊤ : Submodule R M)
    rw [pow_succ', mul_smul]
    exact Submodule.smul_mem_smul ha (f.2 n)
  exact (((reesDenominator R I M).mkQ.restrictScalars R).map_smul a f).symm.trans
    ((Submodule.Quotient.mk_eq_zero (p := reesDenominator R I M) (x := a • f)).mpr hf)

/-- 作用する Rees 代数でも、係数イデアル I の像は随伴次数加群を消す。 -/
lemma ideal_map_le_annihilator_reesGraded :
    I.map (algebraMap R (reesAlgebra I)) ≤
      Module.annihilator (reesAlgebra I) (ReesGraded R I M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro x
  rw [algebraMap_smul]
  exact (Module.mem_annihilator.mp (ideal_le_annihilator_reesGraded R I M ha)) x

/-- 第 n 次の係数を、部分加群 I^nM の元として取り出す。 -/
def reesCoefficient (n : ℕ) : ReesModule R I M →ₗ[R] adicSubmodule R I M n where
  toFun f := ⟨f.1.coeff n, f.2 n⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 第 n 次成分の元を単項式として Rees 加群へ入れる。 -/
def reesSingle (n : ℕ) : adicSubmodule R I M n →ₗ[R] ReesModule R I M :=
  ((lsingle R n).comp (adicSubmodule R I M n).subtype).codRestrict
    ((ReesModule R I M).restrictScalars R) (by
    intro x i
    simp only [LinearMap.comp_apply, lsingle_apply]
    split_ifs with hi
    · subst i; exact x.2
    · exact Submodule.zero_mem _)

@[simp]
lemma reesCoefficient_reesSingle (n : ℕ) (x : adicSubmodule R I M n) :
    reesCoefficient R I M n (reesSingle R I M n x) = x := by
  apply Subtype.ext
  change (PolynomialModule.lsingle R n (x : M)).coeff n = (x : M)
  simp only [lsingle_apply, ite_true]

/-- 係数を対応する次数の商へ落とす写像。 -/
def gradedCoefficient (n : ℕ) : ReesGraded R I M →ₗ[R] GradedPiece R I M n :=
  ((reesDenominator R I M).restrictScalars R).liftQ
    ((gradedDenominator R I M n).mkQ.comp (reesCoefficient R I M n)) (by
      intro f hf
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (mem_reesDenominator R I M f).mp hf n)

/-- I の元 a に対応する Rees 代数の次数一の元 a t。 -/
def reesDegreeOne (a : I) : reesAlgebra I :=
  ⟨Polynomial.monomial 1 (a : R), reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using a.2)⟩

lemma reesDegreeOne_smul_reesSingle (a : I) (n : ℕ) (x : adicSubmodule R I M n) :
    reesDegreeOne R I a • reesSingle R I M n x =
      reesSingle R I M (n + 1) (adicMultiplication R I M a n x) := by
  apply Subtype.ext
  change Polynomial.monomial 1 (a : R) • PolynomialModule.single R n (x : M) =
    PolynomialModule.single R (n + 1) ((a : R) • (x : M))
  rw [PolynomialModule.monomial_smul_single, Nat.add_comm 1 n]

/-- 第 n 次の商を、単項式の剰余類として随伴次数加群へ入れる。 -/
def gradedSingle (n : ℕ) : GradedPiece R I M n →ₗ[R] ReesGraded R I M :=
  (gradedDenominator R I M n).liftQ
    (((reesDenominator R I M).mkQ.restrictScalars R).comp (reesSingle R I M n)) (by
      intro x hx
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rw [mem_reesDenominator]
      intro j
      change (PolynomialModule.lsingle R n (x : M)).coeff j ∈ _
      rw [lsingle_apply]
      split_ifs with hj
      · subst j; exact hx
      · exact Submodule.zero_mem _)

@[simp]
lemma gradedSingle_mk (n : ℕ) (x : adicSubmodule R I M n) :
    gradedSingle R I M n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (reesSingle R I M n x) := rfl

@[simp]
lemma gradedCoefficient_gradedSingle_self (n : ℕ) (x : GradedPiece R I M n) :
    gradedCoefficient R I M n (gradedSingle R I M n x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (gradedDenominator R I M n).mkQ
    (reesCoefficient R I M n (reesSingle R I M n x)) = _
  rw [reesCoefficient_reesSingle]
  rfl

lemma gradedCoefficient_gradedSingle_ne (n m : ℕ) (hnm : m ≠ n)
    (x : GradedPiece R I M m) :
    gradedCoefficient R I M n (gradedSingle R I M m x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (gradedDenominator R I M n).mkQ
    (reesCoefficient R I M n (reesSingle R I M m x)) = 0
  have hc : reesCoefficient R I M n (reesSingle R I M m x) = 0 := by
    apply Subtype.ext
    change (PolynomialModule.lsingle R m (x : M)).coeff n = 0
    simp only [PolynomialModule.lsingle_apply, ite_eq_right hnm]
  rw [hc, map_zero]

/-- Rees 代数の次数一の作用は、各商の次数一の乗法と両立する。 -/
lemma reesDegreeOne_smul_gradedSingle (a : I) (n : ℕ) (x : GradedPiece R I M n) :
    reesDegreeOne R I a • gradedSingle R I M n x =
      gradedSingle R I M (n + 1) (gradedMultiplication R I M a n x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [gradedMultiplication_mk, gradedSingle_mk, gradedSingle_mk]
  exact ((reesDenominator R I M).mkQ.map_smul (reesDegreeOne R I a)
    (reesSingle R I M n x)).symm.trans
    (congrArg (reesDenominator R I M).mkQ (reesDegreeOne_smul_reesSingle R I M a n x))

/-- 各次数の商の直和から、Rees 加群による商表示への写像。 -/
def directSumToReesGraded : (⨁ n, GradedPiece R I M n) →ₗ[R] ReesGraded R I M :=
  DirectSum.toModule R ℕ _ (gradedSingle R I M)

lemma gradedCoefficient_comp_directSumToReesGraded (n : ℕ) :
    (gradedCoefficient R I M n).comp (directSumToReesGraded R I M) =
      DirectSum.component R ℕ (GradedPiece R I M) n := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, directSumToReesGraded, DirectSum.toModule_lof]
  by_cases h : m = n
  · subst m; simp
  · rw [gradedCoefficient_gradedSingle_ne R I M n m h]
    change 0 = (DirectSum.of (GradedPiece R I M) m x) n
    exact (DFinsupp.single_eq_of_ne (Ne.symm h)).symm

lemma directSumToReesGraded_injective : Function.Injective (directSumToReesGraded R I M) := by
  intro x y hxy
  apply DFinsupp.ext
  intro n
  have h := congrArg (gradedCoefficient R I M n) hxy
  change (DirectSum.component R ℕ (GradedPiece R I M) n) x =
    (DirectSum.component R ℕ (GradedPiece R I M) n) y
  simpa only [← gradedCoefficient_comp_directSumToReesGraded R I M n,
    LinearMap.comp_apply] using h

lemma reesModule_as_sum (f : ReesModule R I M) :
    f = ∑ n ∈ f.1.coeff.support, reesSingle R I M n ⟨f.1.coeff n, f.2 n⟩ := by
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  simp only [Submodule.coe_sum, PolynomialModule.coeff_sum]
  change f.1.coeff = ∑ n ∈ f.1.coeff.support, Finsupp.single n (f.1.coeff n)
  exact (Finsupp.sum_single _).symm

lemma directSumToReesGraded_surjective : Function.Surjective (directSumToReesGraded R I M) := by
  intro x
  obtain ⟨f, rfl⟩ := (reesDenominator R I M).mkQ_surjective x
  refine ⟨∑ n ∈ f.1.coeff.support, DirectSum.lof R ℕ (GradedPiece R I M) n
    ((gradedDenominator R I M n).mkQ ⟨f.1.coeff n, f.2 n⟩), ?_⟩
  simp only [map_sum, directSumToReesGraded, DirectSum.toModule_lof,
    Submodule.mkQ_apply, gradedSingle_mk]
  change (∑ n ∈ f.1.coeff.support, (reesDenominator R I M).mkQ
    (reesSingle R I M n ⟨f.1.coeff n, f.2 n⟩)) = (reesDenominator R I M).mkQ f
  rw [← map_sum, ← reesModule_as_sum]

/-- `gr_I(M)` の直和表示と Rees 加群の商表示の R 線形同型。 -/
def directSumReesGradedEquiv : (⨁ n, GradedPiece R I M n) ≃ₗ[R] ReesGraded R I M :=
  LinearEquiv.ofBijective (directSumToReesGraded R I M)
    ⟨directSumToReesGraded_injective R I M, directSumToReesGraded_surjective R I M⟩

end SerrePositivity.HilbertSamuel
