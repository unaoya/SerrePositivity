module

public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialDelta

/-! # 階乗生成部分環の実δ安定性とraw像の同定

Witt繰上り項の部分環内閉性を含めて生成帰納法を検証する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
namespace DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 同じ部分環内の2元のWitt加法繰上り項は、同じ部分環内にある。 -/
theorem additionCarry_mem_subring (S : Subring A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ S := by
  let xS : S := ⟨x, hx⟩
  let yS : S := ⟨y, hy⟩
  let c : S := (WittVector.teichmuller p xS + WittVector.teichmuller p yS).coeff 1
  have he : (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 = S.subtype c := by
    dsimp only [c]
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]
    rfl
  rw [he]
  exact c.property

/-- 生成元のδが生成部分環内にあれば、生成部分環全体のδが内部にある。 -/
theorem delta_mem_subringClosure (D : DeltaStructure p A) (s : Set A)
    (hs : ∀ x ∈ s, D.delta x ∈ Subring.closure s) (x : A) (hx : x ∈ Subring.closure s) :
    D.delta x ∈ Subring.closure s := by
  let S := Subring.closure s
  induction hx using Subring.closure_induction with
  | mem x hx => exact hs x hx
  | zero => rw [D.delta_zero]; exact S.zero_mem
  | one => rw [D.delta_one]; exact S.zero_mem
  | add x y hx hy hdx hdy =>
      rw [D.delta_add]
      exact S.add_mem (S.add_mem hdx hdy) (additionCarry_mem_subring S hx hy)
  | neg x hx hdx =>
      have hc := additionCarry_mem_subring (p := p) S hx (S.neg_mem hx)
      have h := D.delta_add x (-x)
      rw [add_neg_cancel, D.delta_zero] at h
      have he : D.delta (-x) =
          -(D.delta x + (WittVector.teichmuller p x + WittVector.teichmuller p (-x)).coeff 1) := by
        calc
          _ = (D.delta x + D.delta (-x) +
              (WittVector.teichmuller p x + WittVector.teichmuller p (-x)).coeff 1) -
              D.delta x -
              (WittVector.teichmuller p x + WittVector.teichmuller p (-x)).coeff 1 := by ring
          _ = _ := by rw [← h]; ring
      rw [he]
      exact S.neg_mem (S.add_mem hdx hc)
  | mul x y hx hy hdx hdy =>
      rw [D.delta_mul]
      exact S.add_mem (S.add_mem (S.mul_mem (S.pow_mem hx p) hdy)
        (S.mul_mem hdx (S.pow_mem hy p)))
        (S.mul_mem (S.mul_mem (natCast_mem S p) hdx) hdy)

end DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- p局所性の下で、具体的な階乗生成部分環は既存の局所化δ構造で安定。 -/
theorem pDivisionFactorialSubring_delta_mem (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : σ → A) (t : Localization.Away (p : A))
    (ht : t ∈ pDivisionFactorialSubring p y) :
    (deltaPDivisionAwayStructure D).delta t ∈ pDivisionFactorialSubring p y := by
  apply (deltaPDivisionAwayStructure D).delta_mem_subringClosure _ ?_ t ht
  rintro x (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
  · rw [← deltaPDivisionAwayStructure_base_isDeltaHom D a]
    exact pDivisionFactorialSubring_coeff_mem y (D.delta a)
  · exact pDivisionFactorialValue_delta_mem hlocal D y s n

/-- p局所性だけで、階乗生成部分環はrawφ除算包の実局所化像に一致する。 -/
theorem pDivisionFactorialSubring_eq_raw_range (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : σ → A) :
    pDivisionFactorialSubring p y =
      (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range :=
  pDivisionFactorialSubring_eq_raw_range_of_delta_stable D y hlocal
    (pDivisionFactorialSubring_delta_mem hlocal D y)


/-- φによる捻りを含むraw包の局所化内の像は、基底のδ構造の選び方に依存しない。 -/
theorem deltaPDivisionToAway_range_eq_of_deltaStructure
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D E : DeltaStructure p A) (y : σ → A) :
    (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range =
      (deltaPDivisionToAway E (fun s ↦ E.frobeniusLift (y s))).range :=
  (pDivisionFactorialSubring_eq_raw_range hlocal D y).symm.trans
    (pDivisionFactorialSubring_eq_raw_range hlocal E y)

end SerrePositivity.BhattScholze
