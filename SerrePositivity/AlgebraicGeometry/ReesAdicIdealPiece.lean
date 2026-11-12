module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedIdealProjection
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：Rees の IⁿM の次数成分を元の次数成分の Iⁿ 倍として照合する。
方針：次数への線形射影と、部分加群の包含の像を使う。
規約：自然数次数と、負次数を零に延ばした整数次数の両方を扱う。
使われ方：閉厚化の標準開の核を、元の標準開の Iⁿ 倍として同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- Rees の IⁿM の自然数次数 d の像は、元の d 成分の Iⁿ 倍。 -/
theorem reesAdicProjectivePiece_image_eq_ideal_smul (n d : ℕ) :
    (reesAdicProjectivePiece (ι := ι) I G n d).map
      (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).subtype = I ^ n • G d := by
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxG : x.val ∈ G d := hx
    apply (projectiveHomogeneous_mem_ideal_smul_iff (I ^ n) G d hxG).mp
    simpa only [reesAdicProjectiveSubmodule_eq_ideal_smul] using x.property
  · intro hm
    have hIM : m ∈ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n := by
      rw [reesAdicProjectiveSubmodule_eq_ideal_smul]
      exact (Submodule.smul_mono (show I ^ n ≤ I ^ n from le_rfl)
        (show G d ≤ (⊤ : Submodule R M) from le_top)) hm
    have hle : I ^ n • G d ≤ G d := Submodule.smul_le.mpr
      (fun r hr x hx ↦ (G d).smul_mem r hx)
    exact ⟨⟨m, hIM⟩, hle hm, rfl⟩

/-- 整数への零延長後も、Rees の次数成分の像は同じ Iⁿ 倍。 -/
theorem reesAdicProjectiveIntPiece_image_eq_ideal_smul (n : ℕ) (d : ℤ) :
    (projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n) d).map
      (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).subtype =
        I ^ n • projectiveNatGradingInt G d := by
  by_cases hd : 0 ≤ d
  · simp only [projectiveNatGradingInt, hd, ite_true]
    exact reesAdicProjectivePiece_image_eq_ideal_smul I G n d.toNat
  · simp only [projectiveNatGradingInt, hd, ite_false, Submodule.map_bot,
      Submodule.smul_bot]

end SerrePositivity.AlgebraicGeometry
