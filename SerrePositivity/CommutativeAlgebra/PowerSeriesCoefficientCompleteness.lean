module

public import SerrePositivity.CommutativeAlgebra.AdicCompletenessSup
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # 係数イデアルに沿う冪級数の完備性

有限生成イデアルの拡張への所属は全係数の所属と同値であることをMathlibから再利用し、
各係数のadic極限を取る。変数の有限性・環のNoether性は不要。
-/

public section
namespace SerrePositivity
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

end SerrePositivity
