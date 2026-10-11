module

public import SerrePositivity.CommutativeAlgebra.ReesModule
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # 有限個の生成元による Rees 代数の表示

`I = (z_1,…,z_s)` に対して、`R[X_1,…,X_s] → R[It]` を `X_i ↦ z_i t`
で構成し、全射性を証明する。これによって Rees 加群と随伴次数加群を
有限個の次数一生成元を持つ多項式環上の有限加群として扱える。
-/

@[expose] public noncomputable section

universe u

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

lemma gradedReesPresentation_surjective {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    Function.Surjective (gradedReesPresentation R I z hz) := by
  have hcomp : (gradedReesPresentation R I z hz).toRingHom.comp
      (MvPolynomial.map (Ideal.Quotient.mk I)) =
      (Ideal.Quotient.mk _).comp (reesPresentation R I z hz).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [gradedReesPresentation, reesPresentation]
    · intro i
      simp [gradedReesPresentation]
  have hs := (Ideal.Quotient.mk_surjective (I := I.map (algebraMap R (reesAlgebra I)))).comp
    (reesPresentation_surjective R I z hz)
  change Function.Surjective ((Ideal.Quotient.mk
    (I.map (algebraMap R (reesAlgebra I)))).comp (reesPresentation R I z hz).toRingHom) at hs
  rw [← hcomp] at hs
  exact Function.Surjective.of_comp hs

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

/-- 有限個の生成元を選べば、随伴次数加群は `(R/I)[X_1,…,X_s]` 上有限生成。 -/
theorem reesGraded_finite_over_polynomial [IsNoetherianRing R] [Module.Finite R M]
    {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    let _ := gradedPolynomialModule R I M z hz
    Module.Finite (MvPolynomial (Fin s) (R ⧸ I)) (ReesGraded R I M) := by
  let : Algebra (MvPolynomial (Fin s) (R ⧸ I)) (GradedReesRing R I) :=
    (gradedReesPresentation R I z hz).toRingHom.toAlgebra
  let : Module (GradedReesRing R I) (ReesGraded R I M) := reesGraded_module R I M
  let := gradedPolynomialModule R I M z hz
  let : IsScalarTower (MvPolynomial (Fin s) (R ⧸ I)) (GradedReesRing R I)
      (ReesGraded R I M) := IsScalarTower.of_compHom (MvPolynomial (Fin s) (R ⧸ I))
        (GradedReesRing R I) (ReesGraded R I M)
  let : Module.Finite (MvPolynomial (Fin s) (R ⧸ I)) (GradedReesRing R I) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _)
      (gradedReesPresentation_surjective R I z hz)
  exact Module.Finite.trans (GradedReesRing R I) _

end SerrePositivity.HilbertSamuel
