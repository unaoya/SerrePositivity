module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.ReesPresentation
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import SerrePositivity.HomologicalAlgebra.KoszulDirectedLimit
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.Subquotient
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.HilbertSeries
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.AssociatedGraded
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.AdicEuler
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # 次数付き Koszul 複体とその評価

## 概要

Rees 環上の Koszul 複体の有限性、次数付き Koszul ホモロジー（次数を一つ上げる微分の核と像の次数付け）、
次数付き Koszul 複体、その評価写像、十分高い次数での消滅を扱う。

## 方針

微分は次数を一つ上げるので、核と像の次数付けは `HilbertSamuel/Graded/Subquotient` の一般 API
（`d = 1`）から得る。ホモロジーの次数付けは線形同型で移す。

## 規約

名前空間は `GradedKoszul`（次数付け）と `KoszulMultiplicity`（評価）。

## 使われ方

Rees 環を経由した Koszul 複体の adic な非輪状性（`KoszulMultiplicity/Rees`）。
-/

@[expose] public noncomputable section

universe u v w

section ReesFinite

namespace SerrePositivity.KoszulMultiplicity

open HilbertSamuel CategoryTheory

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

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

end SerrePositivity.KoszulMultiplicity

end ReesFinite

section Homology

namespace SerrePositivity.GradedKoszul

open DirectSum
open SerrePositivity.HilbertSerre
open CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable {R M N L : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup L] [Module R L]

/-- Transport an internal homogeneous decomposition along a linear equivalence. -/
theorem isInternal_map_equiv (NS : ℕ → Submodule R M) [Decomposition NS]
    (e : M ≃ₗ[R] N) : DirectSum.IsInternal (fun n => (NS n).map e.toLinearMap) := by
  let p (n : ℕ) : N →ₗ[R] N :=
    e.toLinearMap.comp ((gradeProjection NS n).comp e.symm.toLinearMap)
  apply isInternal_of_projections (fun n => (NS n).map e.toLinearMap) p
  · intro n x
    obtain ⟨m, hm, heq⟩ := x.2
    change e (gradeProjection NS n (e.symm (x : N))) = x
    rw [← heq]
    change e (gradeProjection NS n (e.symm (e m))) = e m
    rw [e.symm_apply_apply, gradeProjection_same NS n hm]
  · intro n k hkn x
    obtain ⟨m, hm, heq⟩ := x.2
    change e (gradeProjection NS n (e.symm (x : N))) = 0
    rw [← heq]
    change e (gradeProjection NS n (e.symm (e m))) = 0
    rw [e.symm_apply_apply, gradeProjection_ne NS n k hkn hm, map_zero]
  · rw [← Submodule.map_iSup, (Decomposition.isInternal NS).submodule_iSup_eq_top,
      Submodule.map_top, LinearEquiv.range]

/-- The product grading on a product of graded modules is an internal direct sum. -/
theorem isInternal_prod (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R N)
    [Decomposition NS] [Decomposition NT] :
    DirectSum.IsInternal (fun n => (NS n).prod (NT n)) := by
  let p (n : ℕ) : M × N →ₗ[R] M × N :=
    (gradeProjection NS n).prodMap (gradeProjection NT n)
  apply isInternal_of_projections (fun n => (NS n).prod (NT n)) p
  · intro n x
    exact Prod.ext (gradeProjection_same NS n x.2.1) (gradeProjection_same NT n x.2.2)
  · intro n k hkn x
    exact Prod.ext (gradeProjection_ne NS n k hkn x.2.1)
      (gradeProjection_ne NT n k hkn x.2.2)
  · apply top_unique
    intro x _
    have hleft : ∀ m : M, (m, (0 : N)) ∈ ⨆ n, (NS n).prod (NT n) := by
      intro m
      induction m using DirectSum.Decomposition.inductionOn NS with
      | zero => exact Submodule.zero_mem _
      | @homogeneous n m =>
        exact (le_iSup (fun n => (NS n).prod (NT n)) n)
          ⟨m.2, Submodule.zero_mem _⟩
      | add a b ha hb =>
        simpa using Submodule.add_mem (⨆ n, (NS n).prod (NT n)) ha hb
    have hright : ∀ n : N, ((0 : M), n) ∈ ⨆ n, (NS n).prod (NT n) := by
      intro m
      induction m using DirectSum.Decomposition.inductionOn NT with
      | zero => exact Submodule.zero_mem _
      | @homogeneous n m =>
        exact (le_iSup (fun n => (NS n).prod (NT n)) n)
          ⟨Submodule.zero_mem _, m.2⟩
      | add a b ha hb =>
        simpa using Submodule.add_mem (⨆ n, (NS n).prod (NT n)) ha hb
    have hx := Submodule.add_mem (⨆ n, (NS n).prod (NT n)) (hleft x.1) (hright x.2)
    simpa using hx

section homology

variable (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R N) (NU : ℕ → Submodule R L)
variable [Decomposition NS] [Decomposition NT] [Decomposition NU]
variable (f : M →ₗ[R] N) (g : N →ₗ[R] L) (hfg : g.comp f = 0)
variable (hf : ∀ n, ∀ x ∈ NS n, f x ∈ NT (n + 1))
variable (hg : ∀ n, ∀ x ∈ NT n, g x ∈ NU (n + 1))

/-- The boundary map with its codomain restricted to the cycles. -/
def toCycles : M →ₗ[R] g.ker :=
  f.codRestrict g.ker (fun x => by
    change g (f x) = 0
    exact DFunLike.congr_fun hfg x)

/-- The explicit module of homology classes. -/
abbrev LinearHomology := g.ker ⧸ (toCycles f g hfg).range

/-- The homogeneous grading of explicit homology classes. -/
def linearHomologyGrade (n : ℕ) : Submodule R (LinearHomology f g hfg) :=
  quotientGrade (submoduleGrade NT g.ker) (toCycles f g hfg).range n

include hf hg in
theorem isInternal_linearHomologyGrade :
    DirectSum.IsInternal (linearHomologyGrade NT f g hfg) := by
  let : Decomposition (submoduleGrade NT g.ker) :=
    (isInternal_submoduleGrade NT g.ker
      (ker_isHomogeneous_of_degree NT NU g hg)).chooseDecomposition
  apply isInternal_quotientGrade
  apply range_isHomogeneous_of_degree NS (submoduleGrade NT g.ker) (toCycles f g hfg)
  intro n x hx
  exact hf n x hx

/-- The explicit quotient identifies with the categorical homology. -/
def linearHomologyEquiv :
    LinearHomology f g hfg ≃ₗ[R] (CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology :=
  (CategoryTheory.ShortComplex.moduleCatMk f g hfg).moduleCatHomologyIso.toLinearEquiv.symm

/-- The grading of the categorical homology object. -/
def homologyGrade (n : ℕ) :
    Submodule R (CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology :=
  (linearHomologyGrade NT f g hfg n).map (linearHomologyEquiv f g hfg).toLinearMap

include hf hg in
theorem isInternal_homologyGrade : DirectSum.IsInternal (homologyGrade NT f g hfg) := by
  let : Decomposition (linearHomologyGrade NT f g hfg) :=
    (isInternal_linearHomologyGrade NS NT NU f g hfg hf hg).chooseDecomposition
  exact isInternal_map_equiv _ (linearHomologyEquiv f g hfg)

include hf in
/-- If the homogeneous part of homology is zero, a homogeneous cycle is the
boundary of an element in the preceding coefficient grade. -/
theorem exists_boundary_in_grade_of_homologyGrade_eq_bot {k : ℕ} (hk : 0 < k)
    (hzero : homologyGrade NT f g hfg k = ⊥) (y : N)
    (hy : y ∈ NT k) (hgy : g y = 0) :
    ∃ z : M, z ∈ NS (k - 1) ∧ f z = y := by
  let c : g.ker := ⟨y, hgy⟩
  let a : LinearHomology f g hfg := (toCycles f g hfg).range.mkQ c
  have ha : a ∈ linearHomologyGrade NT f g hfg k :=
    ⟨c, hy, rfl⟩
  have hclass : linearHomologyEquiv f g hfg a = 0 := by
    have hmem : linearHomologyEquiv f g hfg a ∈ homologyGrade NT f g hfg k :=
      ⟨a, ha, rfl⟩
    rw [hzero, Submodule.mem_bot] at hmem
    exact hmem
  have hazero : a = 0 :=
    (linearHomologyEquiv f g hfg).injective (hclass.trans (map_zero _).symm)
  have hc : c ∈ (toCycles f g hfg).range :=
    (Submodule.Quotient.mk_eq_zero (p := (toCycles f g hfg).range) (x := c)).mp hazero
  obtain ⟨z, hz⟩ := hc
  have hfz : f z = y := congrArg Subtype.val hz
  refine ⟨gradeProjection NS (k - 1) z, (DirectSum.decompose NS z (k - 1)).2, ?_⟩
  have hp := DFunLike.congr_fun (gradeProjection_comp_of_degree NS NT f hf (k - 1)) z
  simp only [LinearMap.comp_apply] at hp
  rw [hfz, Nat.sub_add_cancel hk, gradeProjection_same NT k hy] at hp
  exact hp.symm

end homology

end SerrePositivity.GradedKoszul

end Homology

section ReesModule

namespace SerrePositivity.GradedKoszul
open SerrePositivity.HilbertSamuel SerrePositivity.HilbertSerre
open scoped DirectSum
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The homogeneous Rees monomials of coefficient degree `n`. -/
def reesModuleGrade (n : ℕ) : Submodule R (ReesModule R I M) :=
  (reesSingle R I M n).range

theorem isInternal_reesModuleGrade : DirectSum.IsInternal (reesModuleGrade R I M) := by
  let p (n : ℕ) : ReesModule R I M →ₗ[R] ReesModule R I M :=
    (reesSingle R I M n).comp (reesCoefficient R I M n)
  apply isInternal_of_projections (reesModuleGrade R I M) p
  · intro n x
    obtain ⟨a, ha⟩ := x.2
    rw [← ha]
    change reesSingle R I M n (reesCoefficient R I M n (reesSingle R I M n a)) = _
    rw [reesCoefficient_reesSingle]
  · intro n k hkn x
    obtain ⟨a, ha⟩ := x.2
    rw [← ha]
    change reesSingle R I M n (reesCoefficient R I M n (reesSingle R I M k a)) = 0
    have hzero : reesCoefficient R I M n (reesSingle R I M k a) = 0 := by
      apply Subtype.ext
      change (Finsupp.single k (a : M)) n = 0
      exact Finsupp.single_eq_of_ne (Ne.symm hkn)
    rw [hzero, map_zero]
  · apply top_unique
    intro x _
    rw [reesModule_as_sum R I M x]
    apply Submodule.sum_mem
    intro n _
    exact (le_iSup (reesModuleGrade R I M) n) ⟨_, rfl⟩

end SerrePositivity.GradedKoszul

end ReesModule

section Complex

namespace SerrePositivity.GradedKoszul

open CategoryTheory Limits
open HomologicalComplex.homotopyCofiber
open SerrePositivity.HilbertSerre SerrePositivity.HilbertSamuel
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

section complexes

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A Koszul complex with an arbitrary coefficient module. -/
abbrev moduleComplex {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S) :=
  (koszulModuleFunctor x).obj M

/-- The complex viewed over the coefficient ring `R`. -/
abbrev restrictComplex (P : CochainComplex (ModuleCat.{u} S) ℤ) :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj
    P

/-- Restrict the Koszul module complex to the coefficient ring. -/
abbrev underlyingComplex {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S) :=
  restrictComplex (R := R) (moduleComplex x M)

/-- Scalar multiplication by an element of `S`, viewed as an `R`-linear map. -/
def scalarOnModule (b : S) (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj M →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj M :=
  ((ModuleCat.restrictScalars (algebraMap R S)).map (b • 𝟙 M)).hom

/-- Restriction of an `S`-linear isomorphism still commutes with `S`-scalars. -/
theorem mapIso_scalar_eq {M N : ModuleCat.{u} S} (e : M ≅ N) (b : S)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj M) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapIso e).toLinearEquiv
        (scalarOnModule (R := R) b M u) =
      scalarOnModule (R := R) b N
        (((ModuleCat.restrictScalars (algebraMap R S)).mapIso e).toLinearEquiv u) :=
  e.toLinearEquiv.map_smul b u

/-- The two-product description of a scalar cone term after restriction. -/
def coneTermEquiv (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q) ≃ₗ[R]
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (P.X (q + 1))) ×
        ((ModuleCat.restrictScalars (algebraMap R S)).obj (P.X q)) :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapIso (scalarConeXIsoProd a P q)).toLinearEquiv

/-- The cone product coordinates commute with scalar multiplication. -/
theorem coneTermEquiv_scalar (a b : S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : ℤ)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q)) :
    coneTermEquiv (R := R) a P q
        (scalarOnModule (R := R) b (((scalarConeFunctor a).obj P).X q) u) =
      (scalarOnModule (R := R) b (P.X (q + 1)) (coneTermEquiv (R := R) a P q u).1,
        scalarOnModule (R := R) b (P.X q) (coneTermEquiv (R := R) a P q u).2) :=
  (scalarConeXIsoProd a P q).toLinearEquiv.map_smul b u

private theorem scalarConeXIsoProd_fst (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : ℤ) :
    (scalarConeXIsoProd a P q).hom ≫ ModuleCat.ofHom (LinearMap.fst S (P.X (q + 1)) (P.X q)) =
      fstX (smulId a P) q (q + 1) rfl :=
  mappingConeTermProdIso_fst (smulId a P) q

private theorem scalarConeXIsoProd_snd (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : ℤ) :
    (scalarConeXIsoProd a P q).hom ≫ ModuleCat.ofHom (LinearMap.snd S (P.X (q + 1)) (P.X q)) =
      sndX (smulId a P) q :=
  mappingConeTermProdIso_snd (smulId a P) q

/-- The first component of the cone differential is the negative old differential. -/
theorem coneTermEquiv_d_fst (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q)) :
    (coneTermEquiv (R := R) a P (q + 1)
      (((ModuleCat.restrictScalars (algebraMap R S)).map
        (((scalarConeFunctor a).obj P).d q (q + 1))).hom u)).1 =
      - (((ModuleCat.restrictScalars (algebraMap R S)).map (P.d (q + 1) (q + 1 + 1))).hom
        (coneTermEquiv (R := R) a P q u).1) := by
  have h := d_fstX (smulId a P) q (q + 1) (q + 1 + 1) rfl rfl
  rw [← scalarConeXIsoProd_fst a P (q + 1), ← scalarConeXIsoProd_fst a P q] at h
  exact congrArg (fun f => f.hom u) h

/-- The second component adds scalar multiplication to the old differential. -/
theorem coneTermEquiv_d_snd (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q)) :
    (coneTermEquiv (R := R) a P (q + 1)
      (((ModuleCat.restrictScalars (algebraMap R S)).map
        (((scalarConeFunctor a).obj P).d q (q + 1))).hom u)).2 =
      ((ModuleCat.restrictScalars (algebraMap R S)).map (a • 𝟙 (P.X (q + 1)))).hom
        (coneTermEquiv (R := R) a P q u).1 +
      ((ModuleCat.restrictScalars (algebraMap R S)).map (P.d q (q + 1))).hom
        (coneTermEquiv (R := R) a P q u).2 := by
  have h := d_sndX (smulId a P) q (q + 1) rfl
  rw [← scalarConeXIsoProd_snd a P (q + 1), ← scalarConeXIsoProd_fst a P q,
    ← scalarConeXIsoProd_snd a P q] at h
  exact congrArg (fun f => f.hom u) h

/-- The coefficient grading on every term, recursively along the cone model. -/
def termGrade : ∀ {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S),
    (ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M)) →
      (q : ℤ) → ℕ → Submodule R ((underlyingComplex (R := R) x M).X q)
  | 0, _, M, N, q, n => if hq : q = 0 then
      (N n).map (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M q hq)).toLinearEquiv.symm.toLinearMap)
      else ⊥
  | h + 1, x, M, N, q, n =>
      ((termGrade (Fin.init x) M N (q + 1) n).prod (termGrade (Fin.init x) M N q n)).map
        (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm.toLinearMap

/-- Every term has its coefficient decomposition. -/
theorem isInternal_termGrade : ∀ {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    [DirectSum.Decomposition N] (q : ℤ),
    DirectSum.IsInternal (termGrade x M N q)
  | 0, x, M, N, _, q => by
    by_cases hq : q = 0
    · simp only [termGrade, dite_eq_left hq]
      exact isInternal_map_equiv N _
    · have hz : IsZero ((moduleComplex x M).X q) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq
      have hz' := (ModuleCat.restrictScalars (algebraMap R S)).map_isZero hz
      have : Subsingleton ((underlyingComplex (R := R) x M).X q) :=
        ModuleCat.isZero_iff_subsingleton.mp hz'
      simp only [termGrade, dite_eq_right hq]
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun m => ⟨0, Subsingleton.elim _ _⟩⟩
  | h + 1, x, M, N, _, q => by
    let : DirectSum.Decomposition (termGrade (Fin.init x) M N (q + 1)) :=
      (isInternal_termGrade (Fin.init x) M N (q + 1)).chooseDecomposition
    let : DirectSum.Decomposition (termGrade (Fin.init x) M N q) :=
      (isInternal_termGrade (Fin.init x) M N q).chooseDecomposition
    let : DirectSum.Decomposition (fun n =>
        (termGrade (Fin.init x) M N (q + 1) n).prod (termGrade (Fin.init x) M N q n)) :=
      (isInternal_prod _ _).chooseDecomposition
    exact isInternal_map_equiv _
      (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm

/-- A scalar of coefficient degree one raises every term grade by one. -/
theorem scalarOnModule_mem_termGrade {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (b : S) (hb : ∀ n, ∀ u ∈ N n, scalarOnModule (R := R) b M u ∈ N (n + 1))
    (q : ℤ) (n : ℕ) (u : (underlyingComplex (R := R) x M).X q)
    (hu : u ∈ termGrade x M N q n) :
    scalarOnModule (R := R) b ((moduleComplex x M).X q) u ∈ termGrade x M N q (n + 1) := by
  induction h generalizing q with
  | zero =>
    by_cases hq : q = 0
    · simp only [termGrade, dite_eq_left hq, Submodule.map_equiv_eq_comap_symm,
        LinearEquiv.symm_symm, Submodule.mem_comap] at hu ⊢
      have he := mapIso_scalar_eq (R := R)
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M q hq) b u
      exact he.symm ▸ hb n _ hu
    · simp only [termGrade, dite_eq_right hq, Submodule.mem_bot] at hu ⊢
      rw [hu, map_zero]
  | succ h ih =>
    simp only [termGrade, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm,
      Submodule.mem_comap, Submodule.mem_prod] at hu ⊢
    have he := coneTermEquiv_scalar (R := R) (x (Fin.last h)) b
      (moduleComplex (Fin.init x) M) q u
    exact ⟨(congrArg Prod.fst he).symm ▸ ih (Fin.init x) (q + 1) _ hu.1,
      (congrArg Prod.snd he).symm ▸ ih (Fin.init x) q _ hu.2⟩

/-- The differential raises the coefficient degree by one; after the Koszul
shift, it preserves internal degree. -/
theorem differential_mem_termGrade {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (hx : ∀ j n, ∀ u ∈ N n, scalarOnModule (R := R) (x j) M u ∈ N (n + 1))
    (q : ℤ) (n : ℕ) (u : (underlyingComplex (R := R) x M).X q)
    (hu : u ∈ termGrade x M N q n) :
    ((underlyingComplex (R := R) x M).d q (q + 1)).hom u ∈
      termGrade x M N (q + 1) (n + 1) := by
  induction h generalizing q with
  | zero =>
    change ((ModuleCat.restrictScalars (algebraMap R S)).map
      (((HomologicalComplex.single _ (.up ℤ) 0).obj M).d q (q + 1))).hom u ∈ _
    rw [HomologicalComplex.single_obj_d, Functor.map_zero]
    exact Submodule.zero_mem _
  | succ h ih =>
    have hinit : ∀ j n, ∀ u ∈ N n,
        scalarOnModule (R := R) (Fin.init x j) M u ∈ N (n + 1) :=
      fun j => hx j.castSucc
    simp only [termGrade, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm,
      Submodule.mem_comap, Submodule.mem_prod] at hu ⊢
    have he1 := coneTermEquiv_d_fst (R := R) (x (Fin.last h))
      (moduleComplex (Fin.init x) M) q u
    have he2 := coneTermEquiv_d_snd (R := R) (x (Fin.last h))
      (moduleComplex (Fin.init x) M) q u
    refine ⟨he1.symm ▸ Submodule.neg_mem _ (ih (Fin.init x) hinit (q + 1) _ hu.1), ?_⟩
    have hs := scalarOnModule_mem_termGrade (Fin.init x) M N (x (Fin.last h))
      (hx (Fin.last h)) (q + 1) n _ hu.1
    have hd := ih (Fin.init x) hinit q _ hu.2
    exact he2.symm ▸ (termGrade (Fin.init x) M N (q + 1) (n + 1)).add_mem hs hd

end complexes

end SerrePositivity.GradedKoszul

end Complex

section Evaluation

namespace SerrePositivity.KoszulMultiplicity

open CategoryTheory GradedKoszul

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M T : ModuleCat.{u} S}

/-- Koszul 射の各項を係数環上の線形射として見る。 -/
def termMap {h : ℕ} (x : Fin h → S) (f : M ⟶ T) (q : ℤ) :
    (underlyingComplex (R := R) x M).X q →ₗ[R] (underlyingComplex (R := R) x T).X q :=
  ((ModuleCat.restrictScalars (algebraMap R S)).map (((koszulModuleFunctor x).map f).f q)).hom

private theorem single_conjugation (x : Fin 0 → S) (f : M ⟶ T) :
    (termMap (R := R) x f 0).comp
      (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M 0 rfl)).toLinearEquiv.symm.toLinearMap) =
      (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (HomologicalComplex.singleObjXIsoOfEq
          (.up ℤ) 0 T 0 rfl)).toLinearEquiv.symm.toLinearMap).comp
          ((ModuleCat.restrictScalars (algebraMap R S)).map f).hom := by
  apply LinearMap.ext
  intro m
  change (((HomologicalComplex.single _ (.up ℤ) 0).map f).f 0)
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv m) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv (f m)
  rw [HomologicalComplex.single_map_f_self]
  simp

private theorem cone_conjugation {h : ℕ} (x : Fin (h + 1) → S) (f : M ⟶ T) (q : ℤ) :
    (termMap (R := R) x f q).comp
      (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm.toLinearMap =
      (coneTermEquiv (R := R) (x (Fin.last h))
        (moduleComplex (Fin.init x) T) q).symm.toLinearMap.comp
        ((termMap (R := R) (Fin.init x) f (q + 1)).prodMap
          (termMap (R := R) (Fin.init x) f q)) := by
  apply LinearMap.ext
  intro m
  apply (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q).injective
  have hn := scalarConeXIsoProd_hom_naturality (x (Fin.last h))
    ((koszulModuleFunctor (Fin.init x)).map f) q
  have he := congrArg (fun g ↦ g.hom
    ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) hn
  change (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q)
      (termMap x f q
        ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) =
    ((termMap (Fin.init x) f (q + 1)).prodMap (termMap (Fin.init x) f q))
      ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q)
        ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) at he
  change (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q)
      (termMap x f q
        ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) =
    (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q)
      ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q).symm
        (((termMap (Fin.init x) f (q + 1)).prodMap (termMap (Fin.init x) f q)) m))
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply] using he

/-- 係数の次数成分の像を、全ての Koszul 項の同じ次数成分へ移す。 -/
theorem map_termGrade {h : ℕ} (x : Fin h → S) (f : M ⟶ T)
    (NM : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (NT : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj T))
    (hmap : ∀ n, (NM n).map ((ModuleCat.restrictScalars (algebraMap R S)).map f).hom = NT n)
    (q : ℤ) (n : ℕ) :
    (termGrade x M NM q n).map (termMap (R := R) x f q) = termGrade x T NT q n := by
  induction h generalizing q with
  | zero =>
      by_cases hq : q = 0
      · subst q
        change ((NM n).map (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
          (HomologicalComplex.singleObjXIsoOfEq
            (.up ℤ) 0 M 0 rfl)).toLinearEquiv.symm.toLinearMap)).map
            (termMap x f 0) = (NT n).map
          (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
            (HomologicalComplex.singleObjXIsoOfEq
              (.up ℤ) 0 T 0 rfl)).toLinearEquiv.symm.toLinearMap)
        rw [← Submodule.map_comp, single_conjugation, Submodule.map_comp, hmap]
      · simp only [termGrade, dite_eq_right hq, Submodule.map_bot]
  | succ h ih =>
      rw [termGrade, termGrade, ← Submodule.map_comp, cone_conjugation,
        Submodule.map_comp, LinearMap.prodMap_map_prod, ih (Fin.init x) (q + 1), ih (Fin.init x) q]

/-- 係数の各次数成分上の単射性を、全ての Koszul 項へ移す。 -/
theorem injOn_termGrade {h : ℕ} (x : Fin h → S) (f : M ⟶ T)
    (NM : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (hinj : ∀ n, Set.InjOn ((ModuleCat.restrictScalars (algebraMap R S)).map f).hom (NM n))
    (q : ℤ) (n : ℕ) : Set.InjOn (termMap (R := R) x f q) (termGrade x M NM q n) := by
  induction h generalizing q with
  | zero =>
      by_cases hq : q = 0
      · subst q
        intro a ha b hb hab
        simp only [termGrade] at ha hb
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        have hc := single_conjugation (R := R) x f
        have hab' := hab
        have hca := DFunLike.congr_fun hc a'
        have hcb := DFunLike.congr_fun hc b'
        have hab'' := hca.symm.trans (hab'.trans hcb)
        have hh :=
          (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
            (HomologicalComplex.singleObjXIsoOfEq
              (.up ℤ) 0 T 0 rfl)).toLinearEquiv.symm).injective hab''
        exact congrArg _ (hinj n ha' hb' hh)
      · intro a ha b hb _
        simp only [termGrade, dite_eq_right hq] at ha hb
        exact ha.trans hb.symm
  | succ h ih =>
      intro a ha b hb hab
      simp only [termGrade] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hc := cone_conjugation (R := R) x f q
      have hab' := hab
      have hca := DFunLike.congr_fun hc a'
      have hcb := DFunLike.congr_fun hc b'
      have hab'' := hca.symm.trans (hab'.trans hcb)
      have hh := (coneTermEquiv (R := R) (x (Fin.last h))
        (moduleComplex (Fin.init x) T) q).symm.injective hab''
      have hfst := ih (Fin.init x) (q + 1) ha'.1 hb'.1 (congrArg Prod.fst hh)
      have hsnd := ih (Fin.init x) q ha'.2 hb'.2 (congrArg Prod.snd hh)
      exact congrArg _ (Prod.ext hfst hsnd)

/-- イデアル倍の係数成分は、全 Koszul 項で同じイデアル倍になる。 -/
theorem termGrade_ideal_smul_top {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (J : ℕ → Ideal R) (q : ℤ) (n : ℕ) :
    termGrade x M (fun k ↦ J k • ⊤) q n =
      (J n • ⊤ : Submodule R ((underlyingComplex (R := R) x M).X q)) := by
  induction h generalizing q with
  | zero =>
      by_cases hq : q = 0
      · simp only [termGrade, dite_eq_left hq, Submodule.map_smul'', Submodule.map_top]
        rw [LinearMap.range_eq_top.mpr (LinearEquiv.surjective _)]
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq
        let : Subsingleton ((underlyingComplex (R := R) x M).X q) :=
          ModuleCat.subsingleton_of_isZero
            ((ModuleCat.restrictScalars (algebraMap R S)).map_isZero hz)
        simp only [termGrade, dite_eq_right hq]
        exact Submodule.eq_bot_of_subsingleton.symm
  | succ h ih =>
      rw [termGrade, ih (Fin.init x) (q + 1), ih (Fin.init x) q,
        ← KoszulMultiplicity.smul_top_prod, Submodule.map_smul'', Submodule.map_top]
      rw [LinearMap.range_eq_top.mpr (LinearEquiv.surjective _)]

end SerrePositivity.KoszulMultiplicity

end Evaluation

section Vanishing

namespace SerrePositivity.GradedKoszul

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
variable (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))

theorem koszul_d_comp_d (q : ℤ) :
    ((underlyingComplex (R := R) x M).d q (q + 1)).hom.comp
      ((underlyingComplex (R := R) x M).d (q - 1) q).hom = 0 :=
  ModuleCat.hom_ext_iff.mp ((underlyingComplex (R := R) x M).d_comp_d (q - 1) q (q + 1))

/-- The categorical homology of the displayed short complex agrees with that
of the original complex. -/
def shortHomologyEquiv (q : ℤ) :
    (ShortComplex.moduleCatMk
      ((underlyingComplex (R := R) x M).d (q - 1) q).hom
      ((underlyingComplex (R := R) x M).d q (q + 1)).hom
      (koszul_d_comp_d x M q)).homology ≃ₗ[R] (underlyingComplex (R := R) x M).homology q := by
  change ((underlyingComplex (R := R) x M).sc' (q - 1) q (q + 1)).homology ≃ₗ[R] _
  exact ((underlyingComplex (R := R) x M).homologyIsoSc' (q - 1) q (q + 1)
    ((ComplexShape.up ℤ).prev_eq' (by change q - 1 + 1 = q; omega))
    ((ComplexShape.up ℤ).next_eq' rfl)).toLinearEquiv.symm

/-- Coefficient-degree components of Koszul homology. -/
def koszulHomologyGrade (q : ℤ) (n : ℕ) :
    Submodule R ((underlyingComplex (R := R) x M).homology q) :=
  (homologyGrade (termGrade x M N q)
    ((underlyingComplex (R := R) x M).d (q - 1) q).hom
    ((underlyingComplex (R := R) x M).d q (q + 1)).hom
    (koszul_d_comp_d x M q) n).map (shortHomologyEquiv x M q).toLinearMap

variable [DirectSum.Decomposition N]
variable (hx : ∀ j n, ∀ u ∈ N n, scalarOnModule (R := R) (x j) M u ∈ N (n + 1))

include hx in
/-- The actual Koszul homology inherits a coefficient-degree decomposition. -/
theorem isInternal_koszulHomologyGrade (q : ℤ) :
    DirectSum.IsInternal (koszulHomologyGrade x M N q) := by
  let : DirectSum.Decomposition (termGrade x M N (q - 1)) :=
    (isInternal_termGrade x M N (q - 1)).chooseDecomposition
  let : DirectSum.Decomposition (termGrade x M N q) :=
    (isInternal_termGrade x M N q).chooseDecomposition
  let : DirectSum.Decomposition (termGrade x M N (q + 1)) :=
    (isInternal_termGrade x M N (q + 1)).chooseDecomposition
  have hf : ∀ n, ∀ u ∈ termGrade x M N (q - 1) n,
      ((underlyingComplex (R := R) x M).d (q - 1) q).hom u ∈ termGrade x M N q (n + 1) := by
    intro n u hu
    have hd := differential_mem_termGrade x M N hx (q - 1) n u hu
    rw [show q - 1 + 1 = q by omega] at hd
    exact hd
  have hg : ∀ n, ∀ u ∈ termGrade x M N q n,
      ((underlyingComplex (R := R) x M).d q (q + 1)).hom u ∈ termGrade x M N (q + 1) (n + 1) :=
    differential_mem_termGrade x M N hx q
  let : DirectSum.Decomposition (homologyGrade (termGrade x M N q)
      ((underlyingComplex (R := R) x M).d (q - 1) q).hom
      ((underlyingComplex (R := R) x M).d q (q + 1)).hom
      (koszul_d_comp_d x M q)) :=
    (isInternal_homologyGrade (termGrade x M N (q - 1)) (termGrade x M N q)
      (termGrade x M N (q + 1)) _ _ (koszul_d_comp_d x M q) hf hg).chooseDecomposition
  exact isInternal_map_equiv _ (shortHomologyEquiv x M q)

include hx in
/-- Finite coefficient-ring homology has only finitely many nonzero grades. -/
theorem exists_bound_koszulHomologyGrade_eq_bot (q : ℤ)
    [Module.Finite R ((underlyingComplex (R := R) x M).homology q)] :
    ∃ b : ℕ, ∀ n ≥ b, koszulHomologyGrade x M N q n = ⊥ := by
  let : DirectSum.Decomposition (koszulHomologyGrade x M N q) :=
    (isInternal_koszulHomologyGrade x M N hx q).chooseDecomposition
  exact HilbertSerre.exists_bound_grade_eq_bot _

include hx in
/-- A homogeneous cycle in a vanishing homology grade has a primitive in the
preceding coefficient grade. -/
theorem exists_koszul_boundary_in_grade {q : ℤ} {k : ℕ} (hk : 0 < k)
    (hzero : koszulHomologyGrade x M N q k = ⊥)
    (y : (underlyingComplex (R := R) x M).X q) (hy : y ∈ termGrade x M N q k)
    (hdy : ((underlyingComplex (R := R) x M).d q (q + 1)).hom y = 0) :
    ∃ z : (underlyingComplex (R := R) x M).X (q - 1),
      z ∈ termGrade x M N (q - 1) (k - 1) ∧
        ((underlyingComplex (R := R) x M).d (q - 1) q).hom z = y := by
  let : DirectSum.Decomposition (termGrade x M N (q - 1)) :=
    (isInternal_termGrade x M N (q - 1)).chooseDecomposition
  let : DirectSum.Decomposition (termGrade x M N q) :=
    (isInternal_termGrade x M N q).chooseDecomposition
  have hf : ∀ n, ∀ u ∈ termGrade x M N (q - 1) n,
      ((underlyingComplex (R := R) x M).d (q - 1) q).hom u ∈ termGrade x M N q (n + 1) := by
    intro n u hu
    have hd := differential_mem_termGrade x M N hx (q - 1) n u hu
    rw [show q - 1 + 1 = q by omega] at hd
    exact hd
  have hshort : homologyGrade (termGrade x M N q)
      ((underlyingComplex (R := R) x M).d (q - 1) q).hom
      ((underlyingComplex (R := R) x M).d q (q + 1)).hom
      (koszul_d_comp_d x M q) k = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro a ha
    have hmem : shortHomologyEquiv x M q a ∈ koszulHomologyGrade x M N q k :=
      ⟨a, ha, rfl⟩
    rw [hzero, Submodule.mem_bot] at hmem
    exact (shortHomologyEquiv x M q).injective (hmem.trans (map_zero _).symm)
  exact exists_boundary_in_grade_of_homologyGrade_eq_bot
    (termGrade x M N (q - 1)) (termGrade x M N q) _ _ (koszul_d_comp_d x M q)
      hf hk hshort y hy hdy

include hx in
/-- Over a finite cochain interval, the high-grade homology vanishing bound
can be chosen uniformly. -/
theorem exists_uniform_bound_koszulHomologyGrade_eq_bot
    (hfinite : ∀ q : ℤ, Module.Finite R ((underlyingComplex (R := R) x M).homology q)) :
    ∃ b : ℕ, ∀ q : ℤ, -(h : ℤ) ≤ q → q ≤ 0 →
      ∀ n ≥ b, koszulHomologyGrade x M N q n = ⊥ := by
  classical
  have hb : ∀ q : ℤ, ∃ b : ℕ, ∀ n ≥ b, koszulHomologyGrade x M N q n = ⊥ := by
    intro q
    let := hfinite q
    exact exists_bound_koszulHomologyGrade_eq_bot x M N hx q
  choose b hb using hb
  refine ⟨(Finset.Icc (-(h : ℤ)) 0).sup b, fun q hqlo hqhi n hn => ?_⟩
  apply hb q n
  exact (Finset.le_sup (f := b) (Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩)).trans hn

/-- A Koszul module complex is supported in cochain degrees `[-h, 0]`. -/
theorem moduleComplex_isZero_term (q : ℤ) (hq : q < -(h : ℤ) ∨ 0 < q) :
    IsZero ((moduleComplex x M).X q) := by
  induction h generalizing q with
  | zero =>
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q (by omega)
  | succ h ih =>
    change IsZero ((CochainComplex.mappingCone
      (smulId (x (Fin.last h)) (moduleComplex (Fin.init x) M))).X q)
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨ih (Fin.init x) (q + 1) (by omega), ih (Fin.init x) q (by omega)⟩

/-- The same bound holds after restriction to the coefficient ring. -/
theorem underlyingComplex_isZero_term (q : ℤ) (hq : q < -(h : ℤ) ∨ 0 < q) :
    IsZero ((underlyingComplex (R := R) x M).X q) :=
  (ModuleCat.restrictScalars (algebraMap R S)).map_isZero (moduleComplex_isZero_term x M q hq)

end SerrePositivity.GradedKoszul

namespace SerrePositivity.GradedKoszul

open CategoryTheory Limits

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (h : ℕ)
variable (M : ModuleCat.{u} (MvPolynomial (Fin h) R))
variable [Module.Finite (MvPolynomial (Fin h) R) M]

/-- Finite polynomial-module Koszul homology remains finite over the base
ring after coefficient restriction. -/
theorem finite_underlying_polynomialKoszul_homology (q : ℤ) :
    Module.Finite R
      ((underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).homology q) := by
  let C := moduleComplex (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M
  let : Module R (C.homology q) :=
    Module.compHom _ (algebraMap R (MvPolynomial (Fin h) R))
  let : IsScalarTower R (MvPolynomial (Fin h) R) (C.homology q) :=
    IsScalarTower.of_compHom R (MvPolynomial (Fin h) R) (C.homology q)
  let : Module.Finite R (C.homology q) :=
    KoszulMultiplicity.finite_koszulModuleFunctor_homology_over_base h M q
  let er : C.homology q ≃ₗ[R]
      ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj (C.sc q).homology) :=
    { toFun := fun a => a
      invFun := fun a => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let : Module.Finite R
      ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj (C.sc q).homology) :=
    Module.Finite.equiv er
  let e := (C.sc q).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R)))
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Uniform high-degree vanishing for Koszul complexes on the polynomial
variables and a finite graded coefficient module. -/
theorem exists_uniform_bound_polynomialKoszulHomologyGrade_eq_bot
    (N : ℕ → Submodule R
      ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj M))
    [DirectSum.Decomposition N]
    (hx : ∀ j n, ∀ u ∈ N n,
      scalarOnModule (R := R) (MvPolynomial.X j : MvPolynomial (Fin h) R) M u ∈ N (n + 1)) :
    ∃ b : ℕ, ∀ q : ℤ, -(h : ℤ) ≤ q → q ≤ 0 → ∀ n ≥ b,
      koszulHomologyGrade (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M N q n = ⊥ :=
  exists_uniform_bound_koszulHomologyGrade_eq_bot _ M N hx
    (finite_underlying_polynomialKoszul_homology h M)

/-- In every sufficiently high coefficient degree, every homogeneous cycle
is a homogeneous boundary. The bound is uniform in the cochain position. -/
theorem exists_uniform_bound_polynomialKoszul_boundary
    (N : ℕ → Submodule R
      ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial (Fin h) R))).obj M))
    [DirectSum.Decomposition N]
    (hx : ∀ j n, ∀ u ∈ N n,
      scalarOnModule (R := R) (MvPolynomial.X j : MvPolynomial (Fin h) R) M u ∈ N (n + 1)) :
    ∃ b : ℕ, 0 < b ∧ ∀ q : ℤ, ∀ k ≥ b,
      ∀ y : (underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).X q,
      y ∈ termGrade (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M N q k →
      ((underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).d q (q + 1)).hom y = 0 →
      ∃ z : (underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).X (q - 1),
        z ∈ termGrade (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M N (q - 1) (k - 1) ∧
          ((underlyingComplex (R := R)
            (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).d (q - 1) q).hom z = y := by
  obtain ⟨b, hb⟩ := exists_uniform_bound_polynomialKoszulHomologyGrade_eq_bot h M N hx
  refine ⟨b + 1, Nat.succ_pos _, fun q k hk y hy hdy => ?_⟩
  by_cases hq : -(h : ℤ) ≤ q ∧ q ≤ 0
  · exact exists_koszul_boundary_in_grade _ M N hx (by omega)
      (hb q hq.1 hq.2 k (by omega)) y hy hdy
  · have hz : IsZero ((underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).X q) :=
      underlyingComplex_isZero_term
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M q (by omega)
    have : Subsingleton ((underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) M).X q) :=
      ModuleCat.subsingleton_of_isZero hz
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end SerrePositivity.GradedKoszul

end Vanishing
