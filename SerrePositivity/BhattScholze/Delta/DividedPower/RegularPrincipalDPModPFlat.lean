module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularPrincipalDPModP
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPQuotientFlat

/-! # 正則階乗部分環の実mod p商の通常平坦性 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "S₀" => pDivisionFactorialSubring p (fun _ : Unit ↦ y)
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "T₀" => S₀ ⧸ Ideal.span {(p : S₀)}
local notation "bar₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 実比較同型を通じて指定した、階乗部分環の実p商の係数環A/p作用。 -/
abbrev regularPrincipalDPModPCoefficientAlgebra : Algebra Q₀ T₀ :=
  ((regularPrincipalDPFactorialModPEquiv hA hpA D y hy).symm.toRingHom.comp
    (algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)))).toAlgebra

set_option maxRecDepth 2048 in
/-- 指定したA/p作用は、元の環の全係数上で階乗部分環の実基底射のp商と一致する。 -/
theorem regularPrincipalDPModPCoefficientAlgebra_mk (a : A) :
    letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
    algebraMap Q₀ T₀ (bar₀ a) =
      Ideal.Quotient.mk _ (pDivisionFactorialBase p (fun _ : Unit ↦ y) a) := by
  let := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
  apply (regularPrincipalDPFactorialModPEquiv hA hpA D y hy).injective
  change regularPrincipalDPFactorialModPEquiv hA hpA D y hy
    ((regularPrincipalDPFactorialModPEquiv hA hpA D y hy).symm
      (algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)) (bar₀ a))) = _
  rw [RingEquiv.apply_symm_apply, regularPrincipalDPFactorialModPEquiv_coeff]

/-- 実p商の比較は、明示した自然係数作用に関するA/p代数同型。 -/
def regularPrincipalDPModPAlgEquiv :
    letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
    T₀ ≃ₐ[Q₀] PrincipalDPPresentation Q₀ (bar₀ y) := by
  letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
  exact { regularPrincipalDPFactorialModPEquiv hA hpA D y hy with
    commutes' := fun _ ↦ (regularPrincipalDPFactorialModPEquiv hA hpA D y hy).apply_symm_apply _ }

/-- 任意のK→A/p作用に対し、p乗商のK平坦性から実階乗部分環のp商のK平坦性を得る。 -/
theorem regularPrincipalDPModP_flat_of_powerQuotient_flat
    {K : Type v} [CommRing K] [Algebra K Q₀]
    (hQ : Module.Flat K (Q₀ ⧸ Ideal.span {(bar₀ y) ^ p})) :
    letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
    letI : Algebra K T₀ := Algebra.compHom T₀ (algebraMap K Q₀)
    Module.Flat K T₀ := by
  let := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
  let : Algebra K T₀ := Algebra.compHom T₀ (algebraMap K Q₀)
  let : IsScalarTower K Q₀ T₀ := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hp : (p : Q₀) = 0 := by
    change Ideal.Quotient.mk _ (p : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let := principalDPPresentation_flat_of_quotient_flat (Fact.out : p.Prime) hp (bar₀ y) hQ
  exact Module.Flat.of_linearEquiv
    ((regularPrincipalDPModPAlgEquiv hA hpA D y hy).restrictScalars K).toLinearEquiv

end SerrePositivity.BhattScholze
