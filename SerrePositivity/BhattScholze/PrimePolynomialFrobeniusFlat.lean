module

public import SerrePositivity.BhattScholze.PolynomialExpandFree
public import Mathlib.FieldTheory.Finite.Basic

/-! # B4-6：素数体係数の多項式Frobeniusの忠実平坦性

FrobeniusがMathlibのexpand射と一致することを証明して、既構成の単項式基底を使う。
混標数の自由δ環のFrobeniusと完備化への接続は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 素数体上の多項式Frobeniusは、係数を固定するexpand射そのもの。 -/
theorem primePolynomial_frobenius_eq_expand :
    frobenius (MvPolynomial σ (ZMod p)) p = (MvPolynomial.expand p).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.C c ^ p = MvPolynomial.expand p (MvPolynomial.C c)
    rw [MvPolynomial.expand_C, ← map_pow, ZMod.pow_card]
  · intro s
    change MvPolynomial.X s ^ p = MvPolynomial.expand p (MvPolynomial.X s)
    rw [MvPolynomial.expand_X]

/-- Frobenius作用を持つ標準ULift多項式環は自由。 -/
theorem primePolynomial_frobenius_moduleFree :
    letI : Algebra (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) :=
      (((ULift.ringEquiv : PolynomialExpandTarget p σ (ZMod p) ≃+*
        MvPolynomial σ (ZMod p)).symm.toRingHom).comp
          (frobenius (MvPolynomial σ (ZMod p)) p)).toAlgebra
    Module.Free (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) := by
  rw [primePolynomial_frobenius_eq_expand]
  exact polynomialExpand_moduleFree p σ (ZMod p) (Fact.out : p.Prime).pos

/-- Frobenius作用を持つ標準ULift多項式環は忠実平坦。 -/
theorem primePolynomial_frobenius_moduleFaithfullyFlat :
    letI : Algebra (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) :=
      (((ULift.ringEquiv : PolynomialExpandTarget p σ (ZMod p) ≃+*
        MvPolynomial σ (ZMod p)).symm.toRingHom).comp
          (frobenius (MvPolynomial σ (ZMod p)) p)).toAlgebra
    Module.FaithfullyFlat (MvPolynomial σ (ZMod p)) (PolynomialExpandTarget p σ (ZMod p)) := by
  rw [primePolynomial_frobenius_eq_expand]
  exact polynomialExpand_moduleFaithfullyFlat p σ (ZMod p) (Fact.out : p.Prime).pos

end SerrePositivity.BhattScholze
