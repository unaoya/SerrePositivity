module

public import SerrePositivity.BhattScholze.DeltaRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations

/-! # δ写像のイデアル冪に対する評価

BS著者公開版Lemma 2.17の連続性に使う代数的評価。
p∈Iならδ(I^{n+1})⊂I^nを証明する。有限生成性・p正則性・完備性は不要。
完備化へのδ構造の延長はここでは構成しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Witt加法繰上りは第2引数を含む任意のイデアルに属する。
商へのWitt射を使い、pを約分しない。 -/
theorem wittAdditionCarry_mem_of_right_mem (I : Ideal R) (x y : R) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  simp

namespace DeltaStructure

/-- pを含むイデアルのn+1乗の元のδは、そのn乗に属する。 -/
theorem delta_mem_pow (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (n : ℕ) (x : R) (hx : x ∈ I ^ (n + 1)) : D.delta x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hmul : x ∈ (I ^ (n + 1)) * I := by simpa [pow_succ] using hx
    have hresult : x ∈ I ^ (n + 1) ∧ D.delta x ∈ I ^ (n + 1) := by
      refine Submodule.mul_induction_on (C := fun z ↦
        z ∈ I ^ (n + 1) ∧ D.delta z ∈ I ^ (n + 1)) hmul ?_ ?_
      · intro a ha b hb
        refine ⟨(I ^ (n + 1)).mul_mem_right b ha, ?_⟩
        rw [D.delta_mul]
        apply (I ^ (n + 1)).add_mem
        · apply (I ^ (n + 1)).add_mem
          · exact (I ^ (n + 1)).mul_mem_right _
              ((I ^ (n + 1)).pow_mem_of_mem ha p (Fact.out : p.Prime).pos)
          · have hm := Ideal.mul_mem_mul (ih a ha)
              (I.pow_mem_of_mem hb p (Fact.out : p.Prime).pos)
            simpa [pow_succ] using hm
        · have hm := Ideal.mul_mem_mul (ih a ha) hp
          have hm' : D.delta a * (p : R) ∈ I ^ (n + 1) := by
            simpa [pow_succ] using hm
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (I ^ (n + 1)).mul_mem_right (D.delta b) hm'
      · intro a b ha hb
        refine ⟨(I ^ (n + 1)).add_mem ha.1 hb.1, ?_⟩
        rw [D.delta_add]
        exact (I ^ (n + 1)).add_mem ((I ^ (n + 1)).add_mem ha.2 hb.2)
          (wittAdditionCarry_mem_of_right_mem (I ^ (n + 1)) a b hb.1)
    exact hresult.2

/-- I^{n+1}の摂動でδの値はI^nの範囲でしか変わらない。
Lemma 2.17の具体的な連続性評価m=n+1。 -/
theorem delta_add_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hy : y ∈ I ^ (n + 1)) :
    D.delta (x + y) - D.delta x ∈ I ^ n := by
  rw [D.delta_add]
  have hc := wittAdditionCarry_mem_of_right_mem (p := p) (I ^ (n + 1)) x y hy
  have h := (I ^ n).add_mem (D.delta_mem_pow I hp n y hy)
    (Ideal.pow_le_pow_right (by omega : n ≤ n + 1) hc)
  convert h using 1; ring

/-- x,yがmod I^{n+1}で一致すればδx,δyはmod I^nで一致する。 -/
theorem delta_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hxy : x - y ∈ I ^ (n + 1)) :
    D.delta x - D.delta y ∈ I ^ n := by
  have h := D.delta_add_sub_mem_pow I hp n y (x - y) hxy
  simpa only [add_sub_cancel] using h

end DeltaStructure
end SerrePositivity.BhattScholze
