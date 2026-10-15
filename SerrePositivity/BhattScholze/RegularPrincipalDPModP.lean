module

public import SerrePositivity.BhattScholze.PrincipalDPModP
public import SerrePositivity.BhattScholze.PrincipalDPFactorialEquiv

/-! # 正則一元階乗部分環の実mod p比較 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "S₀" => pDivisionFactorialSubring p (fun _ : Unit ↦ y)
local notation "R₀" => PrincipalDPPresentation A y
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "bar₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 実表示環同型の逆により、階乗部分環のp主イデアルは表示環のp主イデアルへ写る。 -/
theorem regularPrincipalDPFactorialInverse_map_p :
    Ideal.span {(p : R₀)} = (Ideal.span {(p : S₀)}).map
      (principalDPFactorialEquiv hA hpA D y hy).symm.toRingHom := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 具体的階乗部分環の実p商と、係数環のp商上の一元分冪表示環の環同型。 -/
def regularPrincipalDPFactorialModPEquiv :
    (S₀ ⧸ Ideal.span {(p : S₀)}) ≃+* PrincipalDPPresentation Q₀ (bar₀ y) :=
  (Ideal.quotientEquiv _ _ (principalDPFactorialEquiv hA hpA D y hy).symm
    (regularPrincipalDPFactorialInverse_map_p hA hpA D y hy)).trans (principalDPModPEquiv p y)

/-- 実mod p比較は、元の環の全基底係数の商像を対応する係数へ送る。 -/
theorem regularPrincipalDPFactorialModPEquiv_coeff (a : A) :
    regularPrincipalDPFactorialModPEquiv hA hpA D y hy
      (Ideal.Quotient.mk _ (pDivisionFactorialBase p (fun _ : Unit ↦ y) a)) =
      algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)) (bar₀ a) := by
  rw [regularPrincipalDPFactorialModPEquiv, RingEquiv.trans_apply]
  change principalDPModPEquiv p y (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
    ((principalDPFactorialEquiv hA hpA D y hy).symm
      (pDivisionFactorialBase p (fun _ : Unit ↦ y) a))) = _
  rw [← principalDPFactorialEquiv_coeff hA hpA D y hy a, RingEquiv.symm_apply_apply,
    principalDPModPEquiv_coeff]

/-- 実mod p比較は、全階乗生成元の商像を標準生成元へ送る。 -/
theorem regularPrincipalDPFactorialModPEquiv_generator (n : ℕ) :
    regularPrincipalDPFactorialModPEquiv hA hpA D y hy
      (Ideal.Quotient.mk _ (⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ : S₀)) =
      principalDPGenerator (bar₀ y) n := by
  rw [regularPrincipalDPFactorialModPEquiv, RingEquiv.trans_apply]
  change principalDPModPEquiv p y (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
    ((principalDPFactorialEquiv hA hpA D y hy).symm
      (⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ : S₀))) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hy n, RingEquiv.symm_apply_apply,
    principalDPModPEquiv_generator]

end SerrePositivity.BhattScholze
