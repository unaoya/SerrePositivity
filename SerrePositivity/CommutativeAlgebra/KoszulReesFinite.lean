module

public import SerrePositivity.CommutativeAlgebra.ReesPresentation
public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import SerrePositivity.HomologicalAlgebra.KoszulDirectedLimit
public import SerrePositivity.PerfectComplex.Support

/-! # Rees 加群と冪零変数をもつ多項式加群の有限性

Rees 代数の多項式表示に沿って Rees 加群を有限生成多項式加群として扱う。
有限生成多項式加群で全変数が冪零作用するなら、係数環上でも有限生成である。
Koszul ホモロジーの高次数消滅に必要な有限性を供給する。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KoszulReesFinite

open HilbertSamuel CategoryTheory

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Rees 代数の表示 `X_i ↦ z_i t` に沿った Rees 加群への多項式作用。 -/
@[instance_reducible]
def reesPolynomialModule {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    Module (MvPolynomial (Fin s) R) (ReesModule R I M) :=
  Module.compHom _ (reesPresentation R I z hz).toRingHom

/-- 多項式作用は、係数環の既存の作用と両立する。 -/
theorem reesPolynomialModule_scalarTower {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule R I M z hz
    IsScalarTower R (MvPolynomial (Fin s) R) (ReesModule R I M) := by
  let := reesPolynomialModule R I M z hz
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (reesPresentation R I z hz (algebraMap R (MvPolynomial (Fin s) R) r)) • m = r • m
  rw [(reesPresentation R I z hz).commutes]
  exact algebraMap_smul (reesAlgebra I) r m

/-- Noether 環上の有限加群の Rees 加群は、有限個の生成元による多項式環上有限生成。 -/
theorem finite_reesPolynomialModule [IsNoetherianRing R] [Module.Finite R M]
    {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule R I M z hz
    Module.Finite (MvPolynomial (Fin s) R) (ReesModule R I M) := by
  let := reesPolynomialModule R I M z hz
  let : Algebra (MvPolynomial (Fin s) R) (reesAlgebra I) :=
    (reesPresentation R I z hz).toRingHom.toAlgebra
  let : IsScalarTower (MvPolynomial (Fin s) R) (reesAlgebra I) (ReesModule R I M) :=
    IsScalarTower.of_compHom (MvPolynomial (Fin s) R) (reesAlgebra I) (ReesModule R I M)
  let : Module.Finite (MvPolynomial (Fin s) R) (reesAlgebra I) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) (reesPresentation_surjective R I z hz)
  exact Module.Finite.trans (reesAlgebra I) _

section polynomial

variable {R} {σ : Type v} [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]

/-- 全変数が零作用なら、多項式の作用は定数項の作用に等しい。 -/
theorem smul_eq_constantCoeff_of_variables_zero
    (hX : ∀ i : σ, ∀ m : M, (MvPolynomial.X i : MvPolynomial σ R) • m = 0)
    (p : MvPolynomial σ R) (m : M) : p • m = p.constantCoeff • m := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.constantCoeff_C]
      exact algebraMap_smul (MvPolynomial σ R) r m
  | add p q hp hq => rw [add_smul, hp, hq, map_add, add_smul]
  | mul_X p i hp =>
      rw [mul_smul, hX, smul_zero, map_mul, MvPolynomial.constantCoeff_X, mul_zero, zero_smul]

/-- 任意の変数型について、有限生成多項式加群で全変数が零作用なら係数環上有限生成。 -/
theorem finite_of_variables_zero [Module.Finite (MvPolynomial σ R) M]
    (hX : ∀ i : σ, ∀ m : M, (MvPolynomial.X i : MvPolynomial σ R) • m = 0) :
    Module.Finite R M := by
  let f : M →ₛₗ[MvPolynomial.constantCoeff] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun p m ↦ smul_eq_constantCoeff_of_variables_zero M hX p m }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- 有限個の変数がそれぞれ冪零作用する有限生成多項式加群は、係数環上有限生成。
作用の零化イデアルで割ると全変数が整になり、その商環自体が係数環上有限になる。 -/
theorem finite_of_variables_nilpotent [Finite σ] [Module.Finite (MvPolynomial σ R) M]
    (hX : ∀ i : σ, ∃ v : ℕ, 0 < v ∧
      ∀ m : M, (MvPolynomial.X i : MvPolynomial σ R) ^ v • m = 0) :
    Module.Finite R M := by
  classical
  let P := MvPolynomial σ R
  let J := Module.annihilator P M
  let A := P ⧸ J
  let q : P →ₐ[R] A := Ideal.Quotient.mkₐ R J
  let torsion := Module.isTorsionBySet_annihilator P M
  let : Module A M := torsion.module
  let : IsScalarTower R A M := torsion.isScalarTower
  let : Module.Finite A M :=
    Module.Finite.of_surjective torsion.semilinearMap Function.surjective_id
  have hint : ∀ i : σ, IsIntegral R (q (MvPolynomial.X i)) := by
    intro i
    obtain ⟨v, hv, hkill⟩ := hX i
    apply IsIntegral.of_pow hv
    have hzero : q (MvPolynomial.X i) ^ v = 0 := by
      rw [← map_pow]
      change Ideal.Quotient.mk J (MvPolynomial.X i ^ v) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Module.mem_annihilator.mpr hkill)
    rw [hzero]
    exact isIntegral_zero
  have hgen : Algebra.adjoin R (Set.range fun i : σ ↦ q (MvPolynomial.X i)) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    have heq : MvPolynomial.aeval (fun i : σ ↦ q (MvPolynomial.X i)) = q := by
      ext i
      simp
    rw [heq]
    exact (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective
  have hfinite := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.finite_range (fun i : σ ↦ q (MvPolynomial.X i)))
    (by rintro _ ⟨i, rfl⟩; exact hint i)
  rw [hgen] at hfinite
  let : Module.Finite R A := Module.Finite.of_surjective
    ((⊤ : Subalgebra R A).val.toLinearMap) (fun a ↦ ⟨⟨a, trivial⟩, rfl⟩)
  exact Module.Finite.trans A M

end polynomial

section homology

variable {R} [IsNoetherianRing R] {σ : Type} [Finite σ]

/-- 有限生成多項式加群の複体で、ホモロジーへの全変数の作用が冪零なら、
そのホモロジーは係数環上有限生成。係数環作用は既存の作用と両立するものを受け取る。 -/
theorem finite_homology_of_variables_nilpotent
    (C : CochainComplex (ModuleCat.{u} (MvPolynomial σ R)) ℤ) (i : ℤ)
    [Module.Finite (MvPolynomial σ R) (C.X i)]
    [Module R (C.homology i)] [IsScalarTower R (MvPolynomial σ R) (C.homology i)]
    (hX : ∀ j : σ, ∃ v : ℕ, 0 < v ∧
      ∀ m : C.homology i, (MvPolynomial.X j : MvPolynomial σ R) ^ v • m = 0) :
    Module.Finite R (C.homology i) := by
  let : Module.Finite (MvPolynomial σ R) (C.homology i) := homology_moduleFinite C i
  exact finite_of_variables_nilpotent (C.homology i) hX

/-- 特に、ホモロジーへの全変数の作用が零なら係数環上有限生成。 -/
theorem finite_homology_of_variables_zero
    (C : CochainComplex (ModuleCat.{u} (MvPolynomial σ R)) ℤ) (i : ℤ)
    [Module.Finite (MvPolynomial σ R) (C.X i)]
    [Module R (C.homology i)] [IsScalarTower R (MvPolynomial σ R) (C.homology i)]
    (hX : ∀ j : σ, ∀ m : C.homology i, (MvPolynomial.X j : MvPolynomial σ R) • m = 0) :
    Module.Finite R (C.homology i) := by
  let : Module.Finite (MvPolynomial σ R) (C.homology i) := homology_moduleFinite C i
  exact finite_of_variables_zero (C.homology i) hX

end homology

section koszul

variable {R}

/-- 有限生成係数加群の Koszul 構成の各項は有限生成。
空列の単一複体から、錐の項の直積表示によって帰納する。 -/
theorem finite_koszulModuleFunctor_term {h : ℕ} (z : Fin h → R)
    (N : ModuleCat.{u} R) [Module.Finite R N] (i : ℤ) :
    Module.Finite R (((koszulModuleFunctor z).obj N).X i) := by
  induction h generalizing i with
  | zero =>
      change Module.Finite R
        (((HomologicalComplex.single _ (.up ℤ) 0).obj N).X i)
      by_cases hi : i = 0
      · subst i
        exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).toLinearEquiv.symm
      · let : Subsingleton (((HomologicalComplex.single _ (.up ℤ) 0).obj N).X i) :=
          ModuleCat.subsingleton_of_isZero
            (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N i hi)
        infer_instance
  | succ h ih =>
      let K := (koszulModuleFunctor (Fin.init z)).obj N
      let : Module.Finite R (K.X (i + 1)) := ih (Fin.init z) (i + 1)
      let : Module.Finite R (K.X i) := ih (Fin.init z) i
      exact Module.Finite.equiv (scalarConeXIsoProd (z (Fin.last h)) K i).toLinearEquiv.symm

/-- 多項式変数を列とする Koszul 構成のホモロジーは係数環上有限生成。
各変数の冪による零ホモトピーを、上で証明した冪零作用の有限性へ接続する。 -/
theorem finite_koszulModuleFunctor_homology_over_base [IsNoetherianRing R]
    (h : ℕ) (N : ModuleCat.{u} (MvPolynomial (Fin h) R))
    [Module.Finite (MvPolynomial (Fin h) R) N] (i : ℤ)
    [Module R
      (((koszulModuleFunctor (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R)).obj N).homology i)]
    [IsScalarTower R (MvPolynomial (Fin h) R)
      (((koszulModuleFunctor
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R)).obj N).homology i)] :
    Module.Finite R
      (((koszulModuleFunctor
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R)).obj N).homology i) := by
  let X : Fin h → MvPolynomial (Fin h) R := MvPolynomial.X
  let K := (koszulModuleFunctor X).obj N
  let : Module.Finite (MvPolynomial (Fin h) R) (K.X i) :=
    finite_koszulModuleFunctor_term X N i
  change Module.Finite R (K.homology i)
  apply finite_homology_of_variables_nilpotent (R := R) (σ := Fin h) K i
  have hs := (isSupported_koszulComplexOn X
    ((HomologicalComplex.single _ (.up ℤ) 0).obj N)).le_radical_annihilator i
  intro j
  obtain ⟨v, hv⟩ := Ideal.mem_radical_iff.mp (hs (Ideal.subset_span (Set.mem_range_self j)))
  refine ⟨v + 1, Nat.succ_pos _, fun m ↦ ?_⟩
  change X j ^ (v + 1) • m = 0
  have hkill : X j ^ v • m = 0 := (Module.mem_annihilator.mp hv) m
  rw [pow_succ', mul_smul, hkill, smul_zero]

end koszul

end SerrePositivity.KoszulReesFinite
