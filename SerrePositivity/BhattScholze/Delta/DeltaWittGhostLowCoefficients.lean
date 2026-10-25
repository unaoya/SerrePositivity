module

public import SerrePositivity.BhattScholze.Delta.DeltaWittGhostCoefficients

/-! # 構成したWitt元と既存W₂断面の比較

第1ghost公式とp乗算単射だけを用い、全ghost射の単射性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p乗算が単射なら、構成したWitt元の第1係数は既存δ写像に一致する。 -/
theorem deltaWittGhostVector_coeff_one (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a : A) :
    (deltaWittGhostVector D a).coeff 1 = D.delta a := by
  apply hp
  have he := deltaWittGhostVector_ghostComponent D a 1
  rw [witt_ghostComponent_one, deltaWittGhostVector_coeff_zero,
    Function.iterate_one, D.frobeniusLift_apply] at he
  rw [add_comm (a ^ p) ((p : A) * D.delta a)] at he
  exact add_right_cancel he

/-- p乗算単射下で、長さ2への切り詰めは既存のδ構造のW₂断面。 -/
theorem deltaWittGhostVector_truncate_two (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a : A) :
    WittVector.truncate 2 (deltaWittGhostVector D a) = D.sectionHom a := by
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · rw [WittVector.coeff_truncate]
    change (deltaWittGhostVector D a).coeff 0 = (D.sectionHom a).coeff 0
    rw [deltaWittGhostVector_coeff_zero, D.coeff_zero]
  · rw [WittVector.coeff_truncate, deltaWittGhostVector_coeff_one D hp]
    rfl

end SerrePositivity.BhattScholze
