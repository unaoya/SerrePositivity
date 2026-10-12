module

public import SerrePositivity.CommutativeAlgebra.AdicModuleProduct
public import SerrePositivity.CommutativeAlgebra.SamuelModuleProperties
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.PolynomialFiniteDifference
public import SerrePositivity.CategoryTheory.AlternatingSum
public import Mathlib.Algebra.FiniteSupport.Basic

/-! # 有限 adic 商の項の Euler 和

錐の項の直積分解から、フィルトレーション指数についての後退差分を得る。
商の長さの有限性を明示する一般版と、Noether 局所環でそれを供給する適用を分ける。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AdicTermEuler

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-- 項の shifted adic 商の長さ。無限長を零に送る全域定義で、加法性には有限性が必要。 -/
def termLength (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (n q : ℤ) : ℝ :=
  ((HilbertSamuel.samuelFunction R I (P.X q) (n + q).toNat).toNat : ℝ)

/-- 項の adic 長さの交代和。有界性から有限台を確認して計算する。 -/
def euler (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (n : ℤ) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * termLength P I n q

lemma termLength_eq_zero_of_isZero (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Ideal R) (n q : ℤ) (hq : IsZero (P.X q)) : termLength P I n q = 0 := by
  let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp hq
  simp [termLength, HilbertSamuel.samuelFunction, Module.length_eq_zero]

lemma finiteSupport_termLength (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (I : Ideal R) (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) :
    Function.HasFiniteSupport (termLength P I n) := by
  obtain ⟨a, b, hab⟩ := hb
  apply (Set.finite_Icc a b).subset
  intro q hq
  by_contra hnot
  exact hq (termLength_eq_zero_of_isZero P I n q (hab q (by
    simp only [Set.mem_Icc] at hnot
    omega)))


/-- 二つの adic 商の有限性だけから、錐の項の長さを計算する。
環の局所性・Noether 性、項の有限生成性は要求しない。 -/
lemma termLength_cone_of_finite {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (n q : ℤ)
    (hP : HilbertSamuel.samuelFunction R I (P.X (q + 1)) (n + q).toNat ≠ ⊤)
    (hQ : HilbertSamuel.samuelFunction R I (Q.X q) (n + q).toNat ≠ ⊤) :
    termLength (CochainComplex.mappingCone f) I n q =
      termLength P I (n - 1) (q + 1) + termLength Q I n q := by
  let e : (CochainComplex.mappingCone f).X q ≃ₗ[R] (P.X (q + 1) × Q.X q) :=
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv
  dsimp only [termLength]
  rw [show n - 1 + (q + 1) = n + q by ring,
    HilbertSamuel.samuelFunction_eq_of_linearEquiv I e,
    AdicModuleProduct.samuelFunction_prod,
    ENat.toNat_add hP hQ, Nat.cast_add]

/-- 各次数の adic 商の有限性から、錐の項の Euler 和は後退差分になる。
環の局所性・Noether 性や項の有限生成性は要求しない。 -/
theorem euler_cone_of_finite {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (n : ℤ)
    (hP : ∀ q, HilbertSamuel.samuelFunction R I (P.X (q + 1)) (n + q).toNat ≠ ⊤)
    (hQ : ∀ q, HilbertSamuel.samuelFunction R I (Q.X q) (n + q).toNat ≠ ⊤)
    (bP : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (bQ : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (Q.X q)) :
    euler (CochainComplex.mappingCone f) I n = euler Q I n - euler P I (n - 1) := by
  have hflP : Function.HasFiniteSupport (fun q => termLength P I (n - 1) (q + 1)) :=
    (finiteSupport_termLength P I (n - 1) bP).preimage
    (Equiv.addRight (1 : ℤ)).injective.injOn
  have hflQ := finiteSupport_termLength Q I n bQ
  have hwP : Function.HasFiniteSupport
      (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) * termLength P I (n - 1) (q + 1)) :=
    hflP.mul_right _
  have hwQ : Function.HasFiniteSupport
      (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) * termLength Q I n q) := hflQ.mul_right _
  have heq : (fun q : ℤ => ((q.negOnePow : ℤ) : ℝ) *
      termLength (CochainComplex.mappingCone f) I n q) =
      fun q => ((q.negOnePow : ℤ) : ℝ) * termLength P I (n - 1) (q + 1) +
        ((q.negOnePow : ℤ) : ℝ) * termLength Q I n q := by
    funext q
    rw [termLength_cone_of_finite f I n q (hP q) (hQ q), mul_add]
  unfold euler
  rw [heq, finsum_add_distrib hwP hwQ, alternatingFinsum_add_one]
  ring

variable [IsNoetherianRing R] [IsLocalRing R]

/-- 準素 adic 商の有限性を供給する、従来の錐の項の長さ公式。 -/
lemma termLength_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (n q : ℤ)
    [Module.Finite R (P.X (q + 1))] [Module.Finite R (Q.X q)] :
    termLength (CochainComplex.mappingCone f) I n q =
      termLength P I (n - 1) (q + 1) + termLength Q I n q :=
  termLength_cone_of_finite f I n q
    (HilbertSamuel.samuelFunction_ne_top R I hI _ _)
    (HilbertSamuel.samuelFunction_ne_top R I hI _ _)

/-- Noether 局所環の準素商から有限性を供給する、従来の Euler 錐公式。 -/
theorem euler_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (n : ℤ)
    (hP : ∀ q, Module.Finite R (P.X q)) (hQ : ∀ q, Module.Finite R (Q.X q))
    (bP : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (bQ : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (Q.X q)) :
    euler (CochainComplex.mappingCone f) I n = euler Q I n - euler P I (n - 1) := by
  apply euler_cone_of_finite f I n ?_ ?_ bP bQ
  · intro q
    let : Module.Finite R (P.X (q + 1)) := hP _
    exact HilbertSamuel.samuelFunction_ne_top R I hI _ _
  · intro q
    let : Module.Finite R (Q.X q) := hQ _
    exact HilbertSamuel.samuelFunction_ne_top R I hI _ _

end SerrePositivity.AdicTermEuler
