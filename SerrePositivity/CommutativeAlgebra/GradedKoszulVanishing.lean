module

public import SerrePositivity.CommutativeAlgebra.GradedKoszul
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Homogeneous boundary lifting and vanishing for Koszul complexes

The term grading gives a decomposition of each homology module. Finite
generation over the coefficient ring forces high grades to vanish, and then
homogeneous cycles lift to boundaries in the preceding coefficient degree.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.GradedKoszul

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
variable (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))

/-- The two consecutive differentials, as a short complex of underlying modules. -/
def koszulShortComplex (q : ℤ) :=
  (underlyingComplex (R := R) x M).sc' (q - 1) q (q + 1)

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
    KoszulReesFinite.finite_koszulModuleFunctor_homology_over_base h M q
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
