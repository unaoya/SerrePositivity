module

public import SerrePositivity.BhattScholze.PrincipalDPFactorialEquiv
public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialFunctorial

/-! # 正則一元入力の階乗部分環から任意の分冪標的への普遍射

標的のpねじれを許し、標的のδ構造・p局所性・完備性は要求しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
variable (H : DividedPowers I) (hyB : algebraMap A B y ∈ I)
local notation "ys" => fun _ : Unit ↦ y
local notation "S₀" => pDivisionFactorialSubring p ys
local notation "J₀" => pDivisionFactorialIdeal p ys
local notation "HA" => pDivisionFactorialIdealDividedPowers hA D ys
local notation "base₀" => pDivisionFactorialBase p ys
local notation "γ" n => (Subtype.mk (pDivisionFactorialValue p ys () n)
  (pDivisionFactorialSubring_value_mem ys () n) : S₀)

/-- 正則一元入力の階乗部分環から任意の分冪標的への実環射。 -/
def regularPrincipalDPLift : S₀ →+* B :=
  (principalDPEval H y hyB).toRingHom.comp (principalDPFactorialEquiv hA hpA D y hy).symm.toRingHom

include hpA hy hyB

/-- 実普遍射は元のAからの基底射を延長する。 -/
theorem regularPrincipalDPLift_coeff (a : A) :
    regularPrincipalDPLift hA hpA D y hy H hyB (base₀ a) = algebraMap A B a := by
  change principalDPEval H y hyB
    ((principalDPFactorialEquiv hA hpA D y hy).symm (base₀ a)) = _
  rw [← principalDPFactorialEquiv_coeff hA hpA D y hy a, RingEquiv.symm_apply_apply]
  exact AlgHom.commutes (principalDPEval H y hyB) a

/-- 実普遍射は全階乗生成元を標的の指定した分冪値へ送る。 -/
theorem regularPrincipalDPLift_value (n : ℕ) :
    regularPrincipalDPLift hA hpA D y hy H hyB (γ n) = H.dpow n (algebraMap A B y) := by
  change principalDPEval H y hyB ((principalDPFactorialEquiv hA hpA D y hy).symm (γ n)) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hy n, RingEquiv.symm_apply_apply]
  exact principalDPEval_generator H y hyB n

/-- 標的のねじれを許しても、実普遍射は正次数イデアルと全分冪を保つ。 -/
theorem regularPrincipalDPLift_isDPMorphism :
    DividedPowers.IsDPMorphism HA H (regularPrincipalDPLift hA hpA D y hy H hyB) := by
  let F := regularPrincipalDPLift hA hpA D y hy H hyB
  have hbase : base₀ y ∈ J₀ := pDivisionFactorialBase_mem_factorialIdeal ys ()
  have hγ : ∀ n : ℕ, (HA).dpow n (base₀ y) = γ n := by
    intro n
    apply Subtype.ext
    exact pDivisionFactorialIdealDividedPowers_base_apply hA D ys () n
  apply DividedPowers.IsDPMorphism.on_span HA H (S := Set.range (fun z : Unit × ℕ ↦
    (⟨pDivisionFactorialValue p ys z.1 (z.2 + 1),
      pDivisionFactorialSubring_value_mem ys z.1 (z.2 + 1)⟩ : S₀))) rfl
  · rintro a ⟨⟨s, k⟩, rfl⟩
    cases s
    change F (γ (k + 1)) ∈ I
    rw [regularPrincipalDPLift_value]
    exact H.dpow_mem (Nat.succ_ne_zero k) hyB
  · rintro n a ⟨⟨s, k⟩, rfl⟩
    cases s
    change F ((HA).dpow n (γ (k + 1))) = H.dpow n (F (γ (k + 1)))
    rw [← hγ (k + 1), (HA).dpow_comp (Nat.succ_ne_zero k) hbase, map_mul, map_natCast,
      hγ (n * (k + 1)), hγ (k + 1), regularPrincipalDPLift_value,
      regularPrincipalDPLift_value, H.dpow_comp (Nat.succ_ne_zero k) hyB]

/-- 基底射を延長する分冪射は、pねじれを許す任意の分冪標的に一意に存在する。 -/
theorem existsUnique_regularPrincipalDPMorphism :
    ∃! F : S₀ →+* B, F.comp base₀ = algebraMap A B ∧ DividedPowers.IsDPMorphism HA H F := by
  have hbaseF : (regularPrincipalDPLift hA hpA D y hy H hyB).comp base₀ = algebraMap A B := by
    ext a
    exact regularPrincipalDPLift_coeff hA hpA D y hy H hyB a
  refine ⟨regularPrincipalDPLift hA hpA D y hy H hyB,
    ⟨hbaseF, regularPrincipalDPLift_isDPMorphism hA hpA D y hy H hyB⟩, ?_⟩
  intro F hF
  apply pDivisionFactorialHom_ext ys
  · intro a
    exact (RingHom.congr_fun hF.1 a).trans (RingHom.congr_fun hbaseF a).symm
  · intro s n
    cases s
    have hγ : (HA).dpow n (base₀ y) = γ n := by
      apply Subtype.ext
      exact pDivisionFactorialIdealDividedPowers_base_apply hA D ys () n
    calc
      F (γ n) = F ((HA).dpow n (base₀ y)) := congrArg F hγ.symm
      _ = H.dpow n (F (base₀ y)) :=
        (hF.2.dpow_comp _ (pDivisionFactorialBase_mem_factorialIdeal ys ())).symm
      _ = H.dpow n (algebraMap A B y) := congrArg (H.dpow n) (RingHom.congr_fun hF.1 y)
      _ = _ := (regularPrincipalDPLift_value hA hpA D y hy H hyB n).symm

end SerrePositivity.BhattScholze
