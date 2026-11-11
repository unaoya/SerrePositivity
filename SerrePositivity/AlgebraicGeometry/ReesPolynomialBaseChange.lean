module

public import SerrePositivity.AlgebraicGeometry.ReesMap
public import SerrePositivity.AlgebraicGeometry.ReesFiltrationModule
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
概要：基底の Rees 環上の多項式環から、拡大イデアルの Rees 環への全射を作る。
方針：係数には既存の Rees 写像を使い、変数を定数多項式へ送る。
規約：元の変数の次数と Rees の変数の次数を区別する。
使われ方：Rees 加群の有限性を、Rees 環上での射影 Čech 有限性へ移す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] (I : Ideal R)

/-- 基底の Rees 環の係数と、元の多項式の変数を評価する環準同型。 -/
def reesPolynomialBaseChange :
    MvPolynomial ι (reesAlgebra I) →+*
      reesAlgebra (I.map (algebraMap R (MvPolynomial ι R))) :=
  MvPolynomial.eval₂Hom
    (reesMap I (I.map (algebraMap R (MvPolynomial ι R)))
      (algebraMap R (MvPolynomial ι R)) le_rfl)
    (fun i ↦ algebraMap (MvPolynomial ι R) _ (MvPolynomial.X i))

/-- Rees 係数の評価は既存の Rees 写像。 -/
@[simp]
theorem reesPolynomialBaseChange_C (r : reesAlgebra I) :
    reesPolynomialBaseChange (ι := ι) I (MvPolynomial.C r) =
      reesMap I (I.map (algebraMap R (MvPolynomial ι R)))
        (algebraMap R (MvPolynomial ι R)) le_rfl r := by
  simp [reesPolynomialBaseChange]

/-- 元の変数は、拡大イデアルの Rees 環の定数部分へ送る。 -/
@[simp]
theorem reesPolynomialBaseChange_X (i : ι) :
    reesPolynomialBaseChange (ι := ι) I (MvPolynomial.X i) =
      algebraMap (MvPolynomial ι R) _ (MvPolynomial.X i) := by
  simp [reesPolynomialBaseChange]

/-- 元の多項式の係数を基底の Rees 環へ写してから評価すると、定数部分に戻る。 -/
theorem reesPolynomialBaseChange_map (p : MvPolynomial ι R) :
    reesPolynomialBaseChange (ι := ι) I (MvPolynomial.map (algebraMap R (reesAlgebra I)) p) =
      algebraMap (MvPolynomial ι R) _ p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.map_C, reesPolynomialBaseChange_C, reesMap_base]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.map_X, reesPolynomialBaseChange_X, hp]

/-- 拡大イデアルの Rees 環は、基底の Rees 環と元の変数で生成される。 -/
theorem reesPolynomialBaseChange_surjective :
    Function.Surjective (reesPolynomialBaseChange (ι := ι) I) := by
  let P := MvPolynomial ι R
  let B := reesAlgebra I
  let J := I.map (algebraMap R P)
  let Q := MvPolynomial ι B
  let φ := reesPolynomialBaseChange (ι := ι) I
  letI : Algebra P Q := (MvPolynomial.map (algebraMap R B)).toAlgebra
  let e : Q →ₐ[P] Polynomial P :=
    { toRingHom := (reesAlgebra J).val.toRingHom.comp φ
      commutes' := by
        intro p
        exact congrArg Subtype.val (reesPolynomialBaseChange_map I p) }
  have hmono (a : P) (ha : a ∈ J) : Polynomial.monomial 1 a ∈ e.range := by
    change a ∈ Submodule.span P ((algebraMap R P) '' (I : Set R)) at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr, rfl⟩ := ha
      refine ⟨MvPolynomial.C (reesDegreeOne I ⟨r, hr⟩), ?_⟩
      change (φ (MvPolynomial.C (reesDegreeOne I ⟨r, hr⟩))).val = _
      rw [reesPolynomialBaseChange_C, reesMap_degreeOne]
      rfl
    | zero => simpa using e.range.zero_mem
    | add a b ha hb hma hmb =>
      simpa only [map_add] using e.range.add_mem hma hmb
    | smul p a ha hma =>
      have hmul := e.range.mul_mem (e.range.algebraMap_mem p) hma
      change Polynomial.C p * Polynomial.monomial 1 a ∈ e.range at hmul
      rw [Polynomial.C_mul_monomial] at hmul
      exact hmul
  have hle : reesAlgebra J ≤ e.range := by
    rw [← adjoin_monomial_eq_reesAlgebra]
    apply Algebra.adjoin_le
    rintro q ⟨a, ha, rfl⟩
    exact hmono a ha
  intro p
  obtain ⟨q, hq⟩ := hle p.property
  exact ⟨q, Subtype.ext hq⟩

/-- 拡大イデアルの Rees 環上有限な加群は、基底の Rees 環上の多項式環でも有限。 -/
theorem reesPolynomialBaseChange_module_finite
    (N : Type*) [AddCommGroup N]
    [Module (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N]
    [Module.Finite (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N] :
    letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
    Module.Finite (MvPolynomial ι (reesAlgebra I)) N := by
  let P := MvPolynomial ι R
  let Q := MvPolynomial ι (reesAlgebra I)
  let J := I.map (algebraMap R P)
  letI : Algebra Q (reesAlgebra J) := (reesPolynomialBaseChange (ι := ι) I).toAlgebra
  letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
  letI : IsScalarTower Q (reesAlgebra J) N := IsScalarTower.of_compHom Q (reesAlgebra J) N
  letI : Module.Finite Q (reesAlgebra J) :=
    Module.Finite.of_surjective (Algebra.linearMap Q (reesAlgebra J))
      (reesPolynomialBaseChange_surjective I)
  exact Module.Finite.trans (reesAlgebra J) N

/-- Rees 係数の作用と、多項式環に沿う作用は両立する。 -/
theorem reesPolynomialBaseChange_module_scalarTower
    (N : Type*) [AddCommGroup N]
    [Module (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N] :
    letI := Module.compHom N (reesMap I (I.map (algebraMap R (MvPolynomial ι R)))
      (algebraMap R (MvPolynomial ι R)) le_rfl)
    letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I)) N := by
  letI := Module.compHom N (reesMap I (I.map (algebraMap R (MvPolynomial ι R)))
    (algebraMap R (MvPolynomial ι R)) le_rfl)
  letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
  apply IsScalarTower.of_algebraMap_smul
  intro r n
  change reesPolynomialBaseChange (ι := ι) I (MvPolynomial.C r) • n = _
  rw [reesPolynomialBaseChange_C]
  rfl

/-- 元の多項式環からの係数拡大を、基底 Rees 環上の多項式環の代数構造にする。 -/
@[instance_reducible]
def reesPolynomialCoefficientAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  (MvPolynomial.map (algebraMap R (reesAlgebra I))).toAlgebra

/-- 元の多項式環の作用と、基底 Rees 環上の多項式作用も両立する。 -/
theorem reesPolynomialBaseChange_source_scalarTower
    (N : Type*) [AddCommGroup N] [Module (MvPolynomial ι R) N]
    [Module (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N]
    [IsScalarTower (MvPolynomial ι R)
      (reesAlgebra (I.map (algebraMap R (MvPolynomial ι R)))) N] :
    letI := reesPolynomialCoefficientAlgebra (ι := ι) I
    letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) N := by
  letI := reesPolynomialCoefficientAlgebra (ι := ι) I
  letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
  apply IsScalarTower.of_algebraMap_smul
  intro p n
  change reesPolynomialBaseChange (ι := ι) I
    (MvPolynomial.map (algebraMap R (reesAlgebra I)) p) • n = p • n
  rw [reesPolynomialBaseChange_map, algebraMap_smul]

/-- 有限生成多項式加群の I 進 Rees 加群は、基底の Rees 環上の多項式環で有限生成。 -/
theorem reesAdicPolynomialModule_finite [IsNoetherianRing R] [Finite ι]
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial ι R) M]
    [Module.Finite (MvPolynomial ι R) M] :
    let J := I.map (algebraMap R (MvPolynomial ι R))
    let N := (J.stableFiltration (⊤ : Submodule (MvPolynomial ι R) M)).submodule
    letI := Module.compHom N (reesPolynomialBaseChange (ι := ι) I)
    Module.Finite (MvPolynomial ι (reesAlgebra I)) N := by
  let J := I.map (algebraMap R (MvPolynomial ι R))
  let N := (J.stableFiltration (⊤ : Submodule (MvPolynomial ι R) M)).submodule
  letI : Module.Finite (reesAlgebra J) N :=
    reesFiltration_finite _ (J.stableFiltration_stable ⊤)
  exact reesPolynomialBaseChange_module_finite I N

end SerrePositivity.AlgebraicGeometry
