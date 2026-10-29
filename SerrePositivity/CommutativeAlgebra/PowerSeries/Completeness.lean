module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # 冪級数環の完備性

概要：有限生成イデアル `I ⊆ R` について、`R` が `I` 進完備なら `R[[X]]` は `I R[[X]]` 進完備。
`R` が完備 Noether 局所なら、有限変数の `R[[X]]` は `I R[[X]] + (X)` 進完備で、特に極大イデアル進完備。
方針：有限生成イデアルの拡大への所属は全係数の所属と同値（Mathlib の `MvPowerSeries.mem_map_C_iff_of_fg`）
なので、各係数の極限を取る。二つのイデアルの和は、和に沿う完備性の一般論（`AdicCompletenessSup`）へ渡す。
規約：変数の有限性と Noether 性は和の完備性にだけ使う。
使われ方：Cohen–Gabber と Witt の正規化で、正規化する環 `A = k[[X]]` の完備性。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Coefficients

variable {R σ : Type*} [CommRing R]

/-- 係数イデアルの冪による合同を全係数の合同へ移す。 -/
theorem powerSeries_smodEq_coeff_iff (I : Ideal R) (hI : I.FG) (n : ℕ)
    (f g : MvPowerSeries σ R) :
    f ≡ g [SMOD ((I.map (MvPowerSeries.C (σ := σ))) ^ n • ⊤ :
      Ideal (MvPowerSeries σ R))] ↔
      ∀ d, f.coeff d ≡ g.coeff d [SMOD (I ^ n • ⊤ : Ideal R)] := by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow,
    MvPowerSeries.mem_map_C_iff_of_fg hI.pow, map_sub]

/-- I進完備な係数環の冪級数環は、Iの係数拡張に沿って完備。 -/
theorem isAdicComplete_powerSeries_coefficients (I : Ideal R) (hI : I.FG)
    [IsAdicComplete I R] :
    IsAdicComplete (I.map (MvPowerSeries.C (σ := σ))) (MvPowerSeries σ R) := by
  classical
  refine { haus' := ?_, prec' := ?_ }
  · intro f hf
    apply MvPowerSeries.ext
    intro d
    apply IsHausdorff.haus (inferInstance : IsHausdorff I R) (f.coeff d)
    intro n
    simpa using (powerSeries_smodEq_coeff_iff I hI n f 0).mp (hf n) d
  · intro f hf
    have hc (d : σ →₀ ℕ) : ∃ a : R, ∀ n,
        (f n).coeff d ≡ a [SMOD (I ^ n • ⊤ : Ideal R)] := by
      apply IsPrecomplete.prec' (I := I)
      intro m n hmn
      exact (powerSeries_smodEq_coeff_iff I hI m (f m) (f n)).mp (hf hmn) d
    choose a ha using hc
    refine ⟨(fun d ↦ a d : MvPowerSeries σ R), ?_⟩
    intro n
    apply (powerSeries_smodEq_coeff_iff I hI n _ _).mpr
    intro d
    exact ha d n

end Coefficients

section Sup

open IsLocalRing

/-- 完備Noether局所係数環の有限変数冪級数は、係数イデアルと全変数の和について完備。 -/
theorem isAdicComplete_powerSeries_coefficients_sup_variables
    (σ R : Type*) [Finite σ] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete (I.map MvPowerSeries.C ⊔
      Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) (MvPowerSeries σ R) := by
  let : IsAdicComplete (I.map (MvPowerSeries.C (σ := σ))) (MvPowerSeries σ R) :=
    isAdicComplete_powerSeries_coefficients I (IsNoetherian.noetherian I)
  exact isAdicComplete_sup_of_noetherian_local _ _ (powerSeries_variables_le_maximalIdeal σ R)


/-- 完備Noether局所係数環の有限変数冪級数環は極大イデアル進完備。 -/
theorem isAdicComplete_powerSeries_maximalIdeal (σ R : Type*) [Finite σ]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by
  rw [powerSeries_maximalIdeal_eq]
  exact isAdicComplete_powerSeries_coefficients_sup_variables σ R (maximalIdeal R)

end Sup

end SerrePositivity
