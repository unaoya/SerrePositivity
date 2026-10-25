module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPTruncatedAction
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # 実切断多項式環上の一元分冪代数の自由性

零係数環を含む。指定した実作用について自由性と忠実平坦性を証明する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "DA" => DividedPowerAlgebra A A
local notation "T₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- γ_(pk)に沿う、指定された切断多項式作用についての実線形結合写像。 -/
def rankOneDPTruncatedCombination :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    (ℕ →₀ T₀) →ₗ[T₀] DA := by
  letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Finsupp.linearCombination T₀ (fun k : ℕ ↦ DividedPowerAlgebra.dp A (p * k) (1 : A))

/-- 実線形結合写像の一項係数族上の式。 -/
theorem rankOneDPTruncatedCombination_single (k : ℕ) (c : T₀) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedCombination hprime hp (Finsupp.single k c) =
      c • DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Finsupp.linearCombination_single T₀ c k

/-- 実線形結合写像は、零係数環を含めて全単射。 -/
theorem rankOneDPTruncatedCombination_bijective :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Function.Bijective (rankOneDPTruncatedCombination hprime hp) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower A T₀ DA := rankOneDPTruncated_isScalarTower hprime.pos hp
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    let : Subsingleton T₀ := Module.subsingleton A T₀
    let : Subsingleton DA := Module.subsingleton A DA
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun z ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · let := hA
    let bC := rankOneDPTruncatedBasis p A
    let bF : Module.Basis (ℕ × Fin p) A (ℕ →₀ T₀) :=
      (Finsupp.basis (fun _ : ℕ ↦ bC)).reindex (Equiv.sigmaEquivProd ℕ (Fin p))
    let bD := rankOneDPPrimeBlockBasis hprime hp
    let e := bF.equiv bD (Equiv.refl (ℕ × Fin p))
    let L := rankOneDPTruncatedCombination hprime hp
    have he : L.restrictScalars A = e.toLinearMap := by
      apply bF.ext
      rintro ⟨k, r⟩
      change L (bF (k, r)) = e (bF (k, r))
      rw [Module.Basis.equiv_apply]
      change L (((Finsupp.basis (fun _ : ℕ ↦ bC)).reindex
        (Equiv.sigmaEquivProd ℕ (Fin p))) (k, r)) = bD (k, r)
      rw [Module.Basis.reindex_apply]
      simp only [Finsupp.coe_basis]
      change L (Finsupp.single k (bC r)) = bD (k, r)
      rw [rankOneDPTruncatedCombination_single]
      change rankOneDPTruncatedMap hprime.pos hp (rankOneDPTruncatedBasis p A r) *
        DividedPowerAlgebra.dp A (p * k) (1 : A) = rankOneDPPrimeBlockBasis hprime hp (k, r)
      rw [rankOneDPTruncatedMap_basis, rankOneDPPrimeBlockBasis_apply]
    change Function.Bijective (L.restrictScalars A)
    rw [he]
    exact e.bijective

/-- 指定作用に関する、実切断多項式環上の標準自由加群との線形同値。 -/
def rankOneDPTruncatedEquiv :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    (ℕ →₀ T₀) ≃ₗ[T₀] DA := by
  letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact LinearEquiv.ofBijective (rankOneDPTruncatedCombination hprime hp)
    (rankOneDPTruncatedCombination_bijective hprime hp)

/-- 実線形同値の一項係数族上の具体式。 -/
theorem rankOneDPTruncatedEquiv_single (k : ℕ) (c : T₀) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedEquiv hprime hp (Finsupp.single k c) =
      c • DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact rankOneDPTruncatedCombination_single hprime hp k c

/-- 実切断多項式環上でγ_(pk)を基底元とする実基底。 -/
def rankOneDPTruncatedBlockBasis :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Basis ℕ T₀ DA := by
  letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact (Finsupp.basisSingleOne : Module.Basis ℕ T₀ (ℕ →₀ T₀)).map
    (rankOneDPTruncatedEquiv hprime hp)

/-- 実切断多項式環上の各基底元は、指定された分冪生成元γ_(pk)。 -/
theorem rankOneDPTruncatedBlockBasis_apply (k : ℕ) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedBlockBasis hprime hp k = DividedPowerAlgebra.dp A (p * k) (1 : A) := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  rw [rankOneDPTruncatedBlockBasis, Module.Basis.map_apply]
  simp only [Finsupp.coe_basisSingleOne]
  rw [rankOneDPTruncatedEquiv_single, one_smul]

/-- 一元分冪代数は、指定した実切断多項式作用について自由。零環も含む。 -/
theorem rankOneDPTruncated_moduleFree :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Free T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Module.Free.of_basis (rankOneDPTruncatedBlockBasis hprime hp)

/-- 一元分冪代数は、指定した実切断多項式作用について平坦。 -/
theorem rankOneDPTruncated_moduleFlat :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Flat T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  let : Module.Free T₀ DA := rankOneDPTruncated_moduleFree hprime hp
  infer_instance

/-- 一元分冪代数は、指定した実切断多項式作用について忠実平坦。零環も含む。 -/
theorem rankOneDPTruncated_moduleFaithfullyFlat :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.FaithfullyFlat T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hprime.pos hp
  exact Module.FaithfullyFlat.of_linearEquiv T₀ (ℕ →₀ T₀)
    (rankOneDPTruncatedEquiv hprime hp).symm

end SerrePositivity.BhattScholze
