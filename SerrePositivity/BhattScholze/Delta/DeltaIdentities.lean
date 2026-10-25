module

public import SerrePositivity.BhattScholze.Delta.DeltaRing

/-! # δの恒等式とW₂切断の対応

BS著者版Definition 2.1の恒等式を満たす写像からRemark 2.4の切断を構成する。
加法補正項は共通Witt APIの整数係数多項式として扱い、pの正則性を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δの零・単位・加法・積の恒等式からW₂切断を構成する。
座標ごとに環準同型則を確認する（BS Definition 2.1とRemark 2.4の逆向き）。 -/
def ofFunction (δ : A → A) (h0 : δ 0 = 0) (h1 : δ 1 = 0)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)
    (hmul : ∀ x y, δ (x * y) = x ^ p * δ y + δ x * y ^ p + (p : A) * δ x * δ y) :
    DeltaStructure p A := by
  let s : A → WittTwo p A := fun x ↦ TruncatedWittVector.mk p
    (fun i ↦ if i = 0 then x else δ x)
  refine ⟨{ toFun := s
            map_zero' := ?_
            map_one' := ?_
            map_add' := ?_
            map_mul' := ?_ }, ?_⟩
  · apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change (1 : A) = (1 : WittVector p A).coeff 0
      simp
    · change δ 1 = (1 : WittVector p A).coeff 1
      rw [h1, WittVector.one_coeff_eq_of_pos p A 1 (by decide)]
  · intro x y
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change x * y = ((s x).out * (s y).out).coeff 0
      rw [WittVector.mul_coeff_zero]
      simp [s, TruncatedWittVector.out]
    · change δ (x * y) = ((s x).out * (s y).out).coeff 1
      rw [witt_mul_coeff_one]
      simpa [s, TruncatedWittVector.out] using hmul x y
  · apply TruncatedWittVector.ext
    intro i
    fin_cases i <;> simp [s, h0]
  · intro x y
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change x + y = ((s x).out + (s y).out).coeff 0
      rw [WittVector.add_coeff_zero]
      simp [s, TruncatedWittVector.out]
    · change δ (x + y) = ((s x).out + (s y).out).coeff 1
      rw [witt_add_coeff_one]
      simpa [s, TruncatedWittVector.out] using hadd x y
  · intro x
    rfl

/-- 恒等式から構成したδ構造のδ写像は、与えられた写像そのものである。 -/
@[simp] theorem ofFunction_delta (δ : A → A) (h0 : δ 0 = 0) (h1 : δ 1 = 0)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)
    (hmul : ∀ x y, δ (x * y) = x ^ p * δ y + δ x * y ^ p + (p : A) * δ x * δ y)
    (x : A) : (ofFunction δ h0 h1 hadd hmul).delta x = δ x := rfl

/-- δ構造から恒等式を取り出して切断を再構成すると、元の構造に戻る。 -/
@[simp] theorem ofFunction_deltaStructure (D : DeltaStructure p A) :
    ofFunction D.delta D.delta_zero D.delta_one D.delta_add D.delta_mul = D := by
  apply ext
  intro x
  rfl

end SerrePositivity.BhattScholze.DeltaStructure
