module

public import SerrePositivity.BhattScholze.PolynomialExpandDecomposition
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # B4-6：多項式expand射の自由性

Mathlibのexpand射によるスカラー作用を、標準ULift型で通常の係数加群と区別する。
整数の自由δ環の混標数Frobeniusの平坦性とは別のmod p計算。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type u) [CommRing R]

/-- expand作用を持つ加群の型名。台環はMathlibの標準ULift多項式環。 -/
def PolynomialExpandTarget (_n : ℕ) (σ R : Type u) [CommRing R] := ULift.{0} (MvPolynomial σ R)

instance polynomialExpandTargetCommRing : CommRing (PolynomialExpandTarget n σ R) := by
  unfold PolynomialExpandTarget
  infer_instance

/-- expand射によるスカラー作用。標準型ULiftで係数環の通常作用と区別する。 -/
abbrev polynomialExpandAlgebra : Algebra (MvPolynomial σ R) (PolynomialExpandTarget n σ R) :=
  (((ULift.ringEquiv : PolynomialExpandTarget n σ R ≃+* MvPolynomial σ R).symm.toRingHom).comp
    (MvPolynomial.expand n).toRingHom).toAlgebra

attribute [local instance] polynomialExpandAlgebra

/-- 指数がn未満の単項式の、expandによるスカラー作用に関する線形結合。 -/
def polynomialExpandCombination :
    (PolynomialExponentRemainder n σ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      PolynomialExpandTarget n σ R :=
  Finsupp.linearCombination (MvPolynomial σ R) (fun b ↦ ULift.up (MvPolynomial.monomial b.val 1))

/-- 線形結合の単項式上の式。 -/
@[simp] theorem polynomialExpandCombination_single_monomial
    (b : PolynomialExponentRemainder n σ) (q : σ →₀ ℕ) (c : R) :
    polynomialExpandCombination n σ R (Finsupp.single b (MvPolynomial.monomial q c)) =
      ULift.up (MvPolynomial.monomial (n • q + b.val) c) := by
  rw [polynomialExpandCombination, Finsupp.linearCombination_single]
  apply (ULift.ringEquiv : PolynomialExpandTarget n σ R ≃+* MvPolynomial σ R).injective
  change MvPolynomial.expand n (MvPolynomial.monomial q c) *
    MvPolynomial.monomial b.val 1 = MvPolynomial.monomial (n • q + b.val) c
  rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_mul_monomial, mul_one]

/-- 線形結合は、係数の商・余り分解の逆射そのものである。 -/
theorem polynomialExpandCombination_eq_decomposition_symm (hn : 0 < n)
    (f : PolynomialExponentRemainder n σ →₀ MvPolynomial σ R) :
    (polynomialExpandCombination n σ R f).down =
      (polynomialExpandDecomposition n σ R hn).symm f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add]
    change (polynomialExpandCombination n σ R f).down +
      (polynomialExpandCombination n σ R g).down = _
    rw [hf, hg]
  | single b a =>
    induction a using MvPolynomial.induction_on' with
    | add a a' ha ha' =>
      rw [Finsupp.single_add, map_add, map_add]
      change (polynomialExpandCombination n σ R (Finsupp.single b a)).down +
        (polynomialExpandCombination n σ R (Finsupp.single b a')).down = _
      rw [ha, ha']
    | monomial q c =>
      rw [polynomialExpandCombination_single_monomial,
        polynomialExpandDecomposition_symm_single_monomial]

/-- n>0なら、expand作用に関する単項式線形結合は全単射。 -/
theorem polynomialExpandCombination_bijective (hn : 0 < n) :
    Function.Bijective (polynomialExpandCombination n σ R) := by
  have he := polynomialExpandCombination_eq_decomposition_symm n σ R hn
  constructor
  · intro f g h
    apply (polynomialExpandDecomposition n σ R hn).symm.injective
    rw [← he f, ← he g, h]
  · intro x
    refine ⟨polynomialExpandDecomposition n σ R hn x.down, ?_⟩
    apply ULift.ext
    rw [he, LinearEquiv.symm_apply_apply]

/-- expand作用を持つ多項式環の具体的な単項式基底。 -/
def polynomialExpandBasis (hn : 0 < n) :
    Module.Basis (PolynomialExponentRemainder n σ) (MvPolynomial σ R)
      (PolynomialExpandTarget n σ R) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (polynomialExpandCombination n σ R)
    (polynomialExpandCombination_bijective n σ R hn)).symm

/-- expand作用を持つ多項式環は自由加群。 -/
theorem polynomialExpand_moduleFree (hn : 0 < n) :
    Module.Free (MvPolynomial σ R) (PolynomialExpandTarget n σ R) :=
  Module.Free.of_basis (polynomialExpandBasis n σ R hn)

/-- expand作用を持つ多項式環は平坦。 -/
theorem polynomialExpand_moduleFlat (hn : 0 < n) :
    Module.Flat (MvPolynomial σ R) (PolynomialExpandTarget n σ R) := by
  let := polynomialExpand_moduleFree n σ R hn
  infer_instance

/-- 非零係数環ではexpand作用の多項式環は忠実平坦。 -/
theorem polynomialExpand_moduleFaithfullyFlat [Nontrivial R] (hn : 0 < n) :
    Module.FaithfullyFlat (MvPolynomial σ R) (PolynomialExpandTarget n σ R) := by
  let : Nontrivial (PolynomialExpandTarget n σ R) := by
    unfold PolynomialExpandTarget
    infer_instance
  let := polynomialExpand_moduleFree n σ R hn
  infer_instance

end SerrePositivity.BhattScholze
