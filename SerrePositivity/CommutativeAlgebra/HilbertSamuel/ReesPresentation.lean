module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.AssociatedGraded
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # 随伴次数環の多項式環による表示

## 概要

イデアル `I` の生成元 `z_1, …, z_s` から、`R/I` 上の多項式環 `(R/I)[X_1, …, X_s]` → 随伴次数環
`gr_I(R)` の全射な次数付き代数写像（`gradedReesPresentation`）を作り、随伴次数加群がその上の有限生成な
次数付き加群になることを示す。

## 方針

変数 `X_i` を `z_i` の第 1 次成分に送る。全射性は `I^n` が生成元の `n` 次単項式で生成されることによる。

## 規約

名前空間は `HilbertSamuel`。随伴次数環の Noether 性は Mathlib の `isNoetherianRing_reesAlgebra_quotient` を直接使う。

## 使われ方

Hilbert 級数の有理性（`HilbertSamuel/Polynomial`）と正則局所環の表示の単射性（`RegularLocalRing/Graded`）。
-/

@[expose] public noncomputable section

universe u v w

section Presentation

namespace SerrePositivity.HilbertSamuel

variable (R : Type u) [CommRing R] (I : Ideal R)

lemma aeval_range_eq_reesAlgebra {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    (MvPolynomial.aeval (R := R) fun i => Polynomial.monomial 1 (z i)).range = reesAlgebra I := by
  rw [MvPolynomial.aeval_range, ← adjoin_monomial_eq_reesAlgebra,
    ← hz, Submodule.map_span, Algebra.adjoin_span]
  congr 1
  exact Set.range_comp (Polynomial.monomial 1) z

/-- `X_i ↦ z_i t` による多項式環から Rees 代数への表示写像。 -/
def reesPresentation {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    MvPolynomial (Fin s) R →ₐ[R] reesAlgebra I :=
  (MvPolynomial.aeval (R := R) fun i => Polynomial.monomial 1 (z i)).codRestrict _ (by
    intro f
    rw [← aeval_range_eq_reesAlgebra R I z hz]
    exact AlgHom.mem_range_self _ f)

lemma reesPresentation_surjective {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) : Function.Surjective (reesPresentation R I z hz) := by
  intro f
  have hf : f.1 ∈ (MvPolynomial.aeval (R := R) fun i => Polynomial.monomial 1 (z i)).range := by
    rw [aeval_range_eq_reesAlgebra R I z hz]
    exact f.2
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, Subtype.ext hg⟩

@[simp]
lemma reesPresentation_X {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I)
    (i : Fin s) :
    (reesPresentation R I z hz (MvPolynomial.X i) : Polynomial R) = Polynomial.monomial 1 (z i) :=
  MvPolynomial.aeval_X _ _

/-- Rees 代数を係数イデアル I で割った随伴次数環。 -/
abbrev GradedReesRing := reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))

instance gradedReesRing_algebra : Algebra (R ⧸ I) (GradedReesRing R I) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

/-- `R/I` 係数の多項式環による随伴次数環の表示。 -/
def gradedReesPresentation {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    MvPolynomial (Fin s) (R ⧸ I) →ₐ[R ⧸ I] GradedReesRing R I :=
  MvPolynomial.aeval fun i => Ideal.Quotient.mk _
    (reesPresentation R I z hz (MvPolynomial.X i))

/-- 係数を `R` へ持ち上げても、二つの表示は両立する。 -/
theorem gradedReesPresentation_map {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) (p : MvPolynomial (Fin s) R) :
    gradedReesPresentation R I z hz (MvPolynomial.map (Ideal.Quotient.mk I) p) =
      Ideal.Quotient.mk _ (reesPresentation R I z hz p) := by
  have hcomp : (gradedReesPresentation R I z hz).toRingHom.comp
      (MvPolynomial.map (Ideal.Quotient.mk I)) =
      (Ideal.Quotient.mk _).comp (reesPresentation R I z hz).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [gradedReesPresentation, reesPresentation]
    · intro i
      simp [gradedReesPresentation]
  exact DFunLike.congr_fun hcomp p

lemma gradedReesPresentation_surjective {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    Function.Surjective (gradedReesPresentation R I z hz) := by
  have hcomp : (gradedReesPresentation R I z hz).toRingHom.comp
      (MvPolynomial.map (Ideal.Quotient.mk I)) =
      (Ideal.Quotient.mk _).comp (reesPresentation R I z hz).toRingHom :=
    RingHom.ext (gradedReesPresentation_map R I z hz)
  have hs := (Ideal.Quotient.mk_surjective (I := I.map (algebraMap R (reesAlgebra I)))).comp
    (reesPresentation_surjective R I z hz)
  change Function.Surjective ((Ideal.Quotient.mk
    (I.map (algebraMap R (reesAlgebra I)))).comp (reesPresentation R I z hz).toRingHom) at hs
  rw [← hcomp] at hs
  exact Function.Surjective.of_comp hs

section polynomialModule

variable {R I} (N : Type*) [AddCommGroup N] [Module R N] [Module (reesAlgebra I) N]
  [IsScalarTower R (reesAlgebra I) N]

variable (I) in
/-- Rees 代数の表示 `X_i ↦ z_i t` に沿って、`reesAlgebra I` 加群を多項式環 `R[X_1,…,X_s]` 上の加群にする。
Rees 加群・随伴次数加群のどちらにも使う。 -/
@[instance_reducible]
def reesPolynomialModule {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    Module (MvPolynomial (Fin s) R) N :=
  Module.compHom _ (reesPresentation R I z hz).toRingHom

variable (I) in
/-- 多項式作用は係数環の作用と両立する。 -/
lemma reesPolynomialModule_scalarTower {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule I N z hz
    IsScalarTower R (MvPolynomial (Fin s) R) N := by
  let := reesPolynomialModule I N z hz
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (reesPresentation R I z hz (algebraMap R (MvPolynomial (Fin s) R) r)) • x = r • x
  rw [AlgHom.commutes]
  exact algebraMap_smul (reesAlgebra I) r x

variable (I) in
/-- `reesAlgebra I` 上有限な加群は、表示に沿って多項式環上でも有限。 -/
lemma reesPolynomialModule_finite [Module.Finite (reesAlgebra I) N]
    {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule I N z hz
    Module.Finite (MvPolynomial (Fin s) R) N := by
  let : Algebra (MvPolynomial (Fin s) R) (reesAlgebra I) :=
    (reesPresentation R I z hz).toRingHom.toAlgebra
  let := reesPolynomialModule I N z hz
  let : IsScalarTower (MvPolynomial (Fin s) R) (reesAlgebra I) N :=
    IsScalarTower.of_compHom (MvPolynomial (Fin s) R) (reesAlgebra I) N
  let : Module.Finite (MvPolynomial (Fin s) R) (reesAlgebra I) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) (reesPresentation_surjective R I z hz)
  exact Module.Finite.trans (reesAlgebra I) _

end polynomialModule

variable (M : Type u) [AddCommGroup M] [Module R M]

lemma reesGraded_torsionByCoefficients :
    Module.IsTorsionBySet (reesAlgebra I) (ReesGraded R I M)
      (I.map (algebraMap R (reesAlgebra I))) :=
  fun x a => Module.mem_annihilator.mp
    (ideal_map_le_annihilator_reesGraded R I M a.2) x

/-- 随伴次数加群への作用は随伴次数環を経由する。 -/
instance reesGraded_module : Module (GradedReesRing R I) (ReesGraded R I M) :=
  (reesGraded_torsionByCoefficients R I M).module

instance reesGraded_scalarTower :
    IsScalarTower (reesAlgebra I) (GradedReesRing R I) (ReesGraded R I M) :=
  (reesGraded_torsionByCoefficients R I M).isScalarTower

instance reesGraded_finite_over_gradedRing [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite (GradedReesRing R I) (ReesGraded R I M) :=
  Module.Finite.of_restrictScalars_finite (reesAlgebra I) (GradedReesRing R I) _

/-- 表示写像によって、随伴次数加群を `(R/I)[X_1,…,X_s]` 上の加群にする。 -/
@[instance_reducible]
def gradedPolynomialModule {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    Module (MvPolynomial (Fin s) (R ⧸ I)) (ReesGraded R I M) :=
  Module.compHom _ (gradedReesPresentation R I z hz).toRingHom

/-- 各多項式変数は随伴次数加群の次数を一つ上げる。 -/
theorem gradedPolynomial_X_smul_single {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) (i : Fin s) (n : ℕ)
    (x : GradedPiece R I M n) :
    let _ := gradedPolynomialModule R I M z hz
    (MvPolynomial.X i : MvPolynomial (Fin s) (R ⧸ I)) • gradedSingle R I M n x =
      gradedSingle R I M (n + 1) (gradedMultiplication R I M
        ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩ n x) := by
  let a : I := ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  let : Module (GradedReesRing R I) (ReesGraded R I M) := reesGraded_module R I M
  let := gradedPolynomialModule R I M z hz
  change @SMul.smul (GradedReesRing R I) (ReesGraded R I M)
    (reesGraded_module R I M).toSMul
    (gradedReesPresentation R I z hz (MvPolynomial.X i)) (gradedSingle R I M n x) =
      gradedSingle R I M (n + 1) (gradedMultiplication R I M a n x)
  rw [gradedReesPresentation, MvPolynomial.aeval_X]
  change @SMul.smul (reesAlgebra I) (ReesGraded R I M) _
    (reesPresentation R I z hz (MvPolynomial.X i)) (gradedSingle R I M n x) =
    gradedSingle R I M (n + 1) (gradedMultiplication R I M a n x)
  have hr : reesPresentation R I z hz (MvPolynomial.X i) = reesDegreeOne R I a := by
    apply Subtype.ext
    exact reesPresentation_X R I z hz i
  rw [hr]
  exact reesDegreeOne_smul_gradedSingle R I M a n x

end SerrePositivity.HilbertSamuel

end Presentation

section Self

namespace SerrePositivity.HilbertSamuel

open Polynomial PolynomialModule

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)

@[simp]
theorem coeff_equivPolynomialSelf (f : PolynomialModule R R) (n : ℕ) :
    (equivPolynomialSelf f).coeff n = f.coeff n := rfl

@[simp]
theorem coeff_equivPolynomialSelf_symm (f : R[X]) (n : ℕ) :
    (equivPolynomialSelf.symm f).coeff n = f.coeff n := rfl

/-- The Rees module of the ring is the Rees algebra, linearly over that algebra. -/
def reesModuleSelfEquiv : ReesModule R I R ≃ₗ[reesAlgebra I] reesAlgebra I where
  toFun f := ⟨equivPolynomialSelf f.1, by
    intro n
    change f.1.coeff n ∈ I ^ n
    have hf := f.2 n
    change f.1.coeff n ∈ I ^ n • (⊤ : Submodule R R) at hf
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hf⟩
  invFun f := ⟨equivPolynomialSelf.symm f.1, by
    intro n
    change f.1.coeff n ∈ I ^ n • (⊤ : Submodule R R)
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using f.2 n⟩
  left_inv f := by
    apply Subtype.ext
    exact equivPolynomialSelf.symm_apply_apply f.1
  right_inv f := by
    apply Subtype.ext
    exact equivPolynomialSelf.apply_symm_apply f.1
  map_add' f g := by
    apply Subtype.ext
    exact map_add equivPolynomialSelf f.1 g.1
  map_smul' a f := by
    apply Subtype.ext
    change equivPolynomialSelf (a.1 • f.1) = a.1 * equivPolynomialSelf f.1
    exact equivPolynomialSelf.map_smul a.1 f.1

@[simp]
theorem reesModuleSelfEquiv_coeff (f : ReesModule R I R) (n : ℕ) :
    (reesModuleSelfEquiv R I f : R[X]).coeff n = f.1.coeff n := rfl

/-- The shifted Rees denominator corresponds to the image of the coefficient ideal. -/
theorem mem_reesDenominator_iff_self (f : ReesModule R I R) :
    f ∈ reesDenominator R I R ↔
      reesModuleSelfEquiv R I f ∈ I.map (algebraMap R (reesAlgebra I)) := by
  rw [mem_reesDenominator, mem_map_algebraMap_reesAlgebra_iff]
  simp only [reesModuleSelfEquiv_coeff, adicSubmodule_eq, Ideal.smul_eq_mul, Ideal.mul_top]

/-- The denominator is sent onto the coefficient ideal in the Rees algebra. -/
theorem reesDenominator_map_self :
    (reesDenominator R I R).map (reesModuleSelfEquiv R I).toLinearMap =
      I.map (algebraMap R (reesAlgebra I)) := by
  ext f
  rw [Submodule.mem_map]
  refine ⟨fun ⟨g, hg, hgf⟩ => hgf ▸ (mem_reesDenominator_iff_self R I g).mp hg, ?_⟩
  intro hf
  refine ⟨(reesModuleSelfEquiv R I).symm f, ?_, (reesModuleSelfEquiv R I).apply_symm_apply f⟩
  exact (mem_reesDenominator_iff_self R I _).mpr (by simpa using hf)

/-- The self associated graded module is the associated graded ring, linearly over the
Rees algebra. -/
def reesGradedSelfEquiv : ReesGraded R I R ≃ₗ[reesAlgebra I] GradedReesRing R I :=
  Submodule.Quotient.equiv _ _ (reesModuleSelfEquiv R I) (reesDenominator_map_self R I)

@[simp]
theorem reesGradedSelfEquiv_mk (f : ReesModule R I R) :
    reesGradedSelfEquiv R I (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk _ (reesModuleSelfEquiv R I f) := rfl

/-- The same identification is linear over the associated graded ring itself. -/
def reesGradedSelfEquivOverGradedRing :
    ReesGraded R I R ≃ₗ[GradedReesRing R I] GradedReesRing R I where
  toAddEquiv := (reesGradedSelfEquiv R I).toAddEquiv
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := (Ideal.Quotient.mk_surjective
      (I := I.map (algebraMap R (reesAlgebra I)))) a
    change reesGradedSelfEquiv R I
      (@SMul.smul (reesAlgebra I) (ReesGraded R I R) _ r x) =
      @SMul.smul (reesAlgebra I) (GradedReesRing R I) _ r (reesGradedSelfEquiv R I x)
    exact (reesGradedSelfEquiv R I).map_smul r x

@[simp]
theorem reesGradedSelfEquivOverGradedRing_apply (x : ReesGraded R I R) :
    reesGradedSelfEquivOverGradedRing R I x = reesGradedSelfEquiv R I x := rfl

/-- The self Rees monomial corresponds to the ring monomial of the same degree. -/
@[simp]
theorem reesModuleSelfEquiv_reesSingle (n : ℕ) (x : adicSubmodule R I R n) :
    (reesModuleSelfEquiv R I (reesSingle R I R n x) : R[X]) = monomial n (x : R) := by
  change equivPolynomialSelf (single R n (x : R)) = monomial n (x : R)
  rw [equivPolynomialSelf_apply_eq, equivPolynomial_single]

/-- A homogeneous element is sent to its monomial class in the associated graded ring. -/
@[simp]
theorem reesGradedSelfEquiv_gradedSingle_mk (n : ℕ) (x : adicSubmodule R I R n) :
    reesGradedSelfEquiv R I (gradedSingle R I R n (Submodule.Quotient.mk x)) =
      Ideal.Quotient.mk _ (reesModuleSelfEquiv R I (reesSingle R I R n x)) := rfl

end SerrePositivity.HilbertSamuel

end Self
