module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneNormalization

/-!
概要：次数を保つ環写像と、次数一の標準開への正規化の自然性。
方針：既存の Away.map_mk と斉次元の式を直和の環の外延性で照合する。
規約：二つの grading の係数環と宇宙を分ける。
使われ方：任意の係数移送と Segre チャートの写像の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R S A C : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra S C]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable (H : ℕ → Submodule S C) [GradedRing H]
variable (g : G →+*ᵍ H) {f : A} (hf : f ∈ G 1)

/-- 正規化は次数を保つ環写像に自然。係数環は同一と仮定しない。 -/
theorem homogeneousDegreeOneNormalize_naturality (x : A) :
    HomogeneousLocalization.Away.map g f (homogeneousDegreeOneNormalize G hf x) =
      homogeneousDegreeOneNormalize H (g.map_mem hf) (g x) := by
  have he : ((HomogeneousLocalization.Away.map g f).comp
      (homogeneousDegreeOneNormalize G hf)).comp (DirectSum.decomposeRingEquiv G).symm.toRingHom =
      ((homogeneousDegreeOneNormalize H (g.map_mem hf)).comp g.toRingHom).comp
        (DirectSum.decomposeRingEquiv G).symm.toRingHom := by
    apply DirectSum.ringHom_ext
    intro n y
    simp only [RingHom.comp_apply]
    rw [show (DirectSum.decomposeRingEquiv G).symm.toRingHom
      (DirectSum.of (fun n ↦ G n) n y) = (y : A) from DirectSum.decompose_symm_of G y]
    rw [homogeneousDegreeOneNormalize_of_mem G hf y y.property,
      HomogeneousLocalization.Away.map_mk]
    exact (homogeneousDegreeOneNormalize_of_mem H (g.map_mem hf)
      (g.toRingHom y) (g.map_mem y.property)).symm
  have h := RingHom.congr_fun he ((DirectSum.decomposeRingEquiv G) x)
  have hcancel : (DirectSum.decomposeRingEquiv G).symm.toRingHom
      ((DirectSum.decomposeRingEquiv G) x) = x :=
    (DirectSum.decomposeRingEquiv G).symm_apply_apply x
  dsimp only [RingHom.comp_apply] at h
  rw [hcancel] at h
  exact h

end SerrePositivity.AlgebraicGeometry
