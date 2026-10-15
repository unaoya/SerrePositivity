module

public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialStructure
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-! # 正次数の階乗分母の生成イデアルの実分冪構造

既存SubDPIdeal.spanの生成表示を具体的な階乗生成元へ同定する。
分冪包の普遍性は別工程。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
local notation "S₀" => pDivisionFactorialSubring p
local notation "L₀" => Localization.Away (p : A)

/-- 正次数の階乗分母γ_(n+1)(y_s)が生成する、具体的部分環内のイデアル。 -/
def pDivisionFactorialIdeal (p : ℕ) (y : σ → A) : Ideal (pDivisionFactorialSubring p y) :=
  Ideal.span (Set.range (fun z : σ × ℕ ↦
    (⟨pDivisionFactorialValue p y z.1 (z.2 + 1),
      pDivisionFactorialSubring_value_mem y z.1 (z.2 + 1)⟩ : pDivisionFactorialSubring p y)))

omit [Fact p.Prime] in
/-- 各基底元y_sはγ_1(y_s)として、この具体的なイデアルに入る。 -/
theorem pDivisionFactorialBase_mem_factorialIdeal (y : σ → A) (s : σ) :
    pDivisionFactorialBase p y (y s) ∈ pDivisionFactorialIdeal p y := by
  have h := Ideal.subset_span (s := Set.range (fun z : σ × ℕ ↦
    (⟨pDivisionFactorialValue p y z.1 (z.2 + 1),
      pDivisionFactorialSubring_value_mem y z.1 (z.2 + 1)⟩ : S₀ y))) (Set.mem_range_self (s, 0))
  have he : pDivisionFactorialBase p y (y s) =
      (⟨pDivisionFactorialValue p y s 1, pDivisionFactorialSubring_value_mem y s 1⟩ : S₀ y) := by
    apply Subtype.ext
    simp [pDivisionFactorialBase, pDivisionFactorialValue]
  rw [he]
  exact h

/-- 具体的イデアルは、基底元の既存の分冪生成イデアルそのもの。 -/
theorem pDivisionFactorialIdeal_eq_dpSpan
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    pDivisionFactorialIdeal p y =
      (DividedPowers.SubDPIdeal.span (pDivisionFactorialDividedPowers hlocal D y)
        (Set.range (fun s : σ ↦ pDivisionFactorialBase p y (y s)))).carrier := by
  have hS : Set.range (fun s : σ ↦ pDivisionFactorialBase p y (y s)) ⊆
      (pDivisionFactorialDelta hlocal D y).primeDividedPowerIdeal := by
    rintro _ ⟨s, rfl⟩
    exact pDivisionFactorialBase_mem_primeIdeal hlocal D y s
  rw [DividedPowers.SubDPIdeal.span_carrier_eq_dpow_span _ hS]
  apply congrArg Ideal.span
  ext t
  constructor
  · rintro ⟨⟨s, n⟩, rfl⟩
    refine ⟨n + 1, Nat.succ_ne_zero n, pDivisionFactorialBase p y (y s), ⟨s, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (pDivisionFactorialDividedPowers_base_apply hlocal D y s (n + 1)).symm
  · rintro ⟨n, hn, _, ⟨s, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    refine ⟨(s, k), ?_⟩
    apply Subtype.ext
    exact (pDivisionFactorialDividedPowers_base_apply hlocal D y s (k + 1)).symm

/-- 具体的な正次数階乗イデアルは、最大p除算可能イデアルの分冪閉部分イデアル。 -/
theorem pDivisionFactorialIdeal_isSubDPIdeal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    (pDivisionFactorialDividedPowers hlocal D y).IsSubDPIdeal (pDivisionFactorialIdeal p y) := by
  rw [pDivisionFactorialIdeal_eq_dpSpan hlocal D y]
  exact (DividedPowers.SubDPIdeal.span
    (pDivisionFactorialDividedPowers hlocal D y) _).toIsSubDPIdeal

/-- 具体的な正次数階乗イデアル上の、既存APIを制限した実分冪構造。 -/
def pDivisionFactorialIdealDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    DividedPowers (pDivisionFactorialIdeal p y) := by
  classical
  exact DividedPowers.IsSubDPIdeal.dividedPowers (pDivisionFactorialDividedPowers hlocal D y)
    (pDivisionFactorialIdeal_isSubDPIdeal hlocal D y)

/-- 正次数イデアル上の実分冪作用も、基底元で具体的な階乗分母に一致する。 -/
theorem pDivisionFactorialIdealDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    ((pDivisionFactorialIdealDividedPowers hlocal D y).dpow n
      (pDivisionFactorialBase p y (y s)) : L₀) = pDivisionFactorialValue p y s n := by
  classical
  rw [pDivisionFactorialIdealDividedPowers,
    DividedPowers.IsSubDPIdeal.dpow_eq_of_mem (pDivisionFactorialDividedPowers hlocal D y)
      (pDivisionFactorialIdeal_isSubDPIdeal hlocal D y)
      (pDivisionFactorialBase_mem_factorialIdeal (p := p) y s)]
  exact pDivisionFactorialDividedPowers_base_apply hlocal D y s n

end SerrePositivity.BhattScholze
