module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneNormalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：分母を 1 に送る環写像による斉次局所化の特殊化。
方針：通常の局所化の普遍性を制限し、次数ごとの式を直和で照合する。
規約：非零の分母と次数一生成を仮定しない。
使われ方：脱斉次化と A/(f-1) の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v w
variable {R : Type u} {A : Type v} {C : Type w}
variable [CommRing R] [CommRing A] [CommRing C] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
variable (φ : A →+* C) (hφ : φ f = 1)

/-- 分母を 1 に送る環写像による、斉次局所化の特殊化。 -/
def homogeneousDegreeOneSpecialize : HomogeneousLocalization.Away G f →+* C :=
  (Localization.awayLift φ f (isUnit_iff_exists_inv.mpr ⟨1, by simpa using hφ⟩)).comp
    (algebraMap (HomogeneousLocalization.Away G f) (Localization.Away f))

/-- 特殊化は斉次分数の分子を元の環写像で送る。 -/
theorem homogeneousDegreeOneSpecialize_mk (n : ℕ) (x : A) (hx : x ∈ G (n • 1)) :
    homogeneousDegreeOneSpecialize G φ hφ
      (HomogeneousLocalization.Away.mk G hf n x hx) = φ x := by
  change Localization.awayLift φ f (isUnit_iff_exists_inv.mpr ⟨1, by simpa using hφ⟩)
    (Localization.mk x ⟨f ^ n, n, rfl⟩) = _
  rw [Localization.awayLift_mk φ f x 1 (by simpa using hφ)]
  simp

/-- 脱斉次化の後の特殊化は、元の環写像に一致する。 -/
theorem homogeneousDegreeOneSpecialize_normalize (x : A) :
    homogeneousDegreeOneSpecialize G φ hφ (homogeneousDegreeOneNormalize G hf x) = φ x := by
  have heq : ((homogeneousDegreeOneSpecialize G φ hφ).comp
      (homogeneousDegreeOneNormalize G hf)).comp (DirectSum.decomposeRingEquiv G).symm.toRingHom =
      φ.comp (DirectSum.decomposeRingEquiv G).symm.toRingHom := by
    apply DirectSum.ringHom_ext
    intro n y
    simp only [RingHom.comp_apply]
    rw [show (DirectSum.decomposeRingEquiv G).symm.toRingHom (DirectSum.of (fun n ↦ G n) n y) =
      (y : A) from DirectSum.decompose_symm_of G y]
    rw [homogeneousDegreeOneNormalize_of_mem G hf y y.property,
      homogeneousDegreeOneSpecialize_mk G hf φ hφ]
  have h := RingHom.congr_fun heq ((DirectSum.decomposeRingEquiv G) x)
  have hcancel : (DirectSum.decomposeRingEquiv G).symm.toRingHom
      ((DirectSum.decomposeRingEquiv G) x) = x :=
    (DirectSum.decomposeRingEquiv G).symm_apply_apply x
  dsimp only [RingHom.comp_apply] at h
  rw [hcancel] at h
  exact h

/-- 正規化自身による特殊化は斉次局所化の恒等写像。 -/
theorem homogeneousDegreeOneSpecialize_normalize_self (z : HomogeneousLocalization.Away G f) :
    homogeneousDegreeOneSpecialize G (homogeneousDegreeOneNormalize G hf)
      (homogeneousDegreeOneNormalize_self G hf) z = z := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective G hf z
  rw [homogeneousDegreeOneSpecialize_mk G hf,
    homogeneousDegreeOneNormalize_of_mem G hf x (by simpa using hx)]

end SerrePositivity.AlgebraicGeometry
