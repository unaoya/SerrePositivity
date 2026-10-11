module

public import SerrePositivity.CommutativeAlgebra.AssociatedGraded
public import SerrePositivity.CommutativeAlgebra.ArtinReesGrowth
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Lifting regularity from an associated graded module

If the degree-one initial form of `x ∈ I` acts injectively in every degree,
multiplication by `x` has the expected inverse image of every filtration step.
Krull intersection then implies that `x` itself is regular on a finite module
over a Noetherian local ring.
-/

@[expose] public section

universe u

namespace SerrePositivity.HilbertSamuel

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Degreewise regularity gives the exact inverse-image identity for the
filtration. No separatedness or finiteness assumptions are needed here. -/
theorem comap_pow_smul_top_eq_of_gradedMultiplication_injective
    (I : Ideal R) (x : I)
    (hx : ∀ n, Function.Injective (gradedMultiplication R I M x n)) (n : ℕ) :
    (I ^ (n + 1) • ⊤ : Submodule R M).comap (LinearMap.lsmul R M (x : R)) =
      I ^ n • ⊤ := by
  apply le_antisymm
  · intro m hm
    change (x : R) • m ∈ I ^ (n + 1) • (⊤ : Submodule R M) at hm
    induction n with
    | zero => simp
    | succ n ih =>
      have hmn : m ∈ adicSubmodule R I M n := ih
        (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) le_rfl hm)
      let a : adicSubmodule R I M n := ⟨m, hmn⟩
      have hzero : gradedMultiplication R I M x n (Submodule.Quotient.mk a) = 0 := by
        rw [gradedMultiplication_mk, Submodule.Quotient.mk_eq_zero]
        exact hm
      have ha : (Submodule.Quotient.mk a : GradedPiece R I M n) = 0 :=
        hx n (hzero.trans (map_zero _).symm)
      rw [Submodule.Quotient.mk_eq_zero] at ha
      exact ha
  · intro m hm
    exact smul_mem_adicSubmodule R I M x hm

/-- Krull intersection lifts regularity of the initial form to regularity on
the module itself. The ideal may be any proper ideal of the local ring. -/
theorem isSMulRegular_of_gradedMultiplication_injective [IsNoetherianRing R]
    [IsLocalRing R] [Module.Finite R M] (I : Ideal R) (hI : I ≠ ⊤) (x : I)
    (hx : ∀ n, Function.Injective (gradedMultiplication R I M x n)) :
    IsSMulRegular M (x : R) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro m hm
  have hall : m ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.mem_iInf]
    intro n
    rw [← comap_pow_smul_top_eq_of_gradedMultiplication_injective I x hx n]
    change (x : R) • m ∈ I ^ (n + 1) • (⊤ : Submodule R M)
    rw [hm]
    exact Submodule.zero_mem _
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI] at hall
  exact hall

/-- When the initial form is regular, the Samuel function of the scalar
quotient is exactly the first finite difference of that of the module. -/
theorem samuelFunction_succ_eq_add_quotSMulTop_of_gradedMultiplication_injective
    (I : Ideal R) (x : I)
    (hx : ∀ n, Function.Injective (gradedMultiplication R I M x n)) (n : ℕ) :
    samuelFunction R I M (n + 1) = samuelFunction R I M n +
      samuelFunction R I (QuotSMulTop (x : R) M) (n + 1) := by
  rw [samuelFunction_quotSMulTop_eq (M := M) I (x : R) (n + 1),
    comap_pow_smul_top_eq_of_gradedMultiplication_injective I x hx n]
  rfl

end SerrePositivity.HilbertSamuel
