module

public import SerrePositivity.BhattScholze.Delta.DeltaAdicEstimate
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # δの有限I進商への降下

p∈IのもとでδはR/I^{n+1}→R/I^nという集合の写像を定める。
環射や各R/I^nのδ構造ではない。完備化の座標構成に使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- δを一段深い商から浅い商へ降下させた写像。 -/
def adicDeltaStep (D : DeltaStructure p R) (I : Ideal R) (n : ℕ) :
    R ⧸ I ^ (n + 1) → R ⧸ I ^ n :=
  fun x ↦ Ideal.Quotient.mk (I ^ n) (D.delta (Quotient.out x))

/-- p∈Iなら降下写像は代表元のδを取る写像である。 -/
@[simp] theorem adicDeltaStep_mk (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x : R) :
    D.adicDeltaStep I n (Ideal.Quotient.mk (I ^ (n + 1)) x) =
      Ideal.Quotient.mk (I ^ n) (D.delta x) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply D.delta_sub_mem_pow I hp n
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (Ideal.Quotient.mk_out _)

/-- δの一段ずらした写像はI進商の標準遷移と可換。 -/
theorem adicDeltaStep_factorPow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ (n + 1)) :
    Ideal.Quotient.factorPow I hmn (D.adicDeltaStep I n x) =
      D.adicDeltaStep I m (Ideal.Quotient.factorPow I (Nat.add_le_add_right hmn 1) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [D.adicDeltaStep_mk I hp]

end SerrePositivity.BhattScholze.DeltaStructure
