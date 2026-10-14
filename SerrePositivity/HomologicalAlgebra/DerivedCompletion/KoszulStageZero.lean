module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # 各冪のKoszul複体のH⁰と商環の逆系

正則性を仮定せず、各段のH⁰を商加群へ同定する。
商環の標準的な遷移は別に定義する。この同定とKoszul遷移の自然性は次の工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R]

/-- 各元のn乗で生成されるイデアル。一般のイデアル冪と区別する。 -/
def powerKoszulIdeal {e : ℕ} (a : Fin e → R) (n : ℕ) : Ideal R :=
  Ideal.span (Set.range (fun i ↦ a i ^ n))

/-- 各段のH⁰の商加群との同型。正則性やねじれの有界性は不要。
存在証明から一つ選ぶ同型であり、遷移に関する自然性はまだ主張しない。 -/
def powerKoszulStageH0Equiv {e : ℕ} (a : Fin e → R) (n : ℕ) :
    (powerKoszulTower R a n).homology 0 ≃ₗ[R] R ⧸ powerKoszulIdeal R a n :=
  (koszulComplex_homology_zero_equiv (fun i ↦ a i ^ n)).some

/-- 元の冪を進めると、生成されるイデアルは小さくなる。 -/
theorem powerKoszulIdeal_antitone {e : ℕ} (a : Fin e → R) :
    Antitone (powerKoszulIdeal R a) := by
  intro m n hmn
  apply Ideal.span_le.mpr
  rintro z ⟨i, rfl⟩
  change a i ^ n ∈ powerKoszulIdeal R a m
  have heq : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  rw [heq, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

/-- 冪による商環の標準的な遷移写像。 -/
def powerKoszulQuotientTransition {e : ℕ} (a : Fin e → R) (n : ℕ) :
    R ⧸ powerKoszulIdeal R a (n + 1) →+* R ⧸ powerKoszulIdeal R a n :=
  Ideal.Quotient.factor (powerKoszulIdeal_antitone R a (Nat.le_succ n))

@[simp] theorem powerKoszulQuotientTransition_mk {e : ℕ} (a : Fin e → R) (n : ℕ) (r : R) :
    powerKoszulQuotientTransition R a n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 商環の遷移は全射。高次Koszulホモロジーの遷移にはこの結論を使用しない。 -/
theorem powerKoszulQuotientTransition_surjective {e : ℕ} (a : Fin e → R) (n : ℕ) :
    Function.Surjective (powerKoszulQuotientTransition R a n) :=
  Ideal.Quotient.factor_surjective _

end SerrePositivity.DerivedCompletion
